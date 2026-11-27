-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_5_3
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:56:01.610811+00:00
-- url     : https://prove2.me/theorems/2e0d6378-4a3f-4989-b716-4c47f27b2128
-- title:
--   Theorem 5:3 — the further relations (5:6a)–(5:6d), $|r_i|<|p_i|$ and acute angles
-- statement:
--   For the cg-method with a real symmetric positive definite $A$, with $b_i=|r_{i+1}|^2/|r_i|^2$:
--
--   $$(p_i,p_j)=\frac{|r_j|^2|p_i|^2}{|r_i|^2}\ (i\le j),\qquad |p_i|^2=|r_i|^2+b_{i-1}^2|p_{i-1}|^2=|r_i|^4\sum_{j=0}^{i}\frac{1}{|r_j|^2}\ (i>0), \tag{5:6a, 5:6b}$$
--
--   $$(r_i,Ar_j)=0\ (|i-j|>1),\qquad (r_i,Ar_i)=(p_i,Ap_i)+b_{i-1}^2(p_{i-1},Ap_{i-1})\ (i>0). \tag{5:6c, 5:6d}$$
--
--   The vector $r_i$ is shorter than $p_i$: $|r_i|\le|p_i|$ always, with equality at $i=0$ ($p_0=r_0$) and strict inequality for $0<i<m$. Any two nonzero directions make an acute angle: $(p_i,p_j)>0$ for $i,j<m$.
--
--   These relations are the inner-product calculus of the cg-method used throughout §§6–7; (5:6a) alone is the published base item `direction_inner_5_6a`.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - reading: “$r_i$ is shorter than $p_i$”; “$p_i$ makes an acute angle with $p_j$” → $|r_i|^2\le|p_i|^2$ for all $i$ and $<$ for $0<i<m$; $(p_i,p_j)>0$ for $i,j<m$; reason: at $i=0$ the two vectors coincide, and after termination the directions vanish and have no angle
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 415, Theorem 5:3, eqs. (5:6a)–(5:6d) (PDF p. 7)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:3 (Hestenes–Stiefel 1952, p. 415): (5:6a)–(5:6d), `|rᵢ| ≤ |pᵢ|` with strict
inequality for `0 < i < m`, and acute angles between the nonzero directions; `m` is the step at
which the cg-method terminates (`rₘ = 0`, `rⱼ ≠ 0` for `j < m`). (5:6b) and (5:6d) are stated at
the paper's index `i + 1 > 0`. -/
theorem theorem_5_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i j : ℕ, i ≤ j → (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).p =
      ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r) *
        ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) /
        ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r)) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 1)).p ⬝ᵥ (cgIter A k x₀ (i + 1)).p =
        (cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r +
          cgBeta A k x₀ i ^ 2 * ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) ∧
      (cgIter A k x₀ (i + 1)).p ⬝ᵥ (cgIter A k x₀ (i + 1)).p =
        ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) ^ 2 *
          ∑ j ∈ Finset.range (i + 2), 1 / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) ∧
    (∀ i j : ℕ, (i + 1 < j ∨ j + 1 < i) →
      (cgIter A k x₀ i).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).r) = 0) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 1)).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ (i + 1)).r) =
      (cgIter A k x₀ (i + 1)).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ (i + 1)).p) +
        cgBeta A k x₀ i ^ 2 * ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p))) ∧
    (∀ i : ℕ, (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r ≤
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) ∧
    (∀ i : ℕ, 0 < i → i < m → (cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r <
      (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p) ∧
    (∀ i j : ℕ, i < m → j < m → 0 < (cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ j).p) := by sorry

end ConjGrad.ErrorDecrease.Supplement
