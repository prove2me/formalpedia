-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_5_5
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_5_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:57:01.243978+00:00
-- url     : https://prove2.me/theorems/1082f4f6-0c85-4eaa-ba46-c28e779f901e
-- title:
--   Theorem 5:5 — formulas (5:10), (5:11) for $a_i$, $b_i$ and the bounds (5:12)
-- statement:
--   For the cg-method with a real symmetric positive definite $A$ and Rayleigh quotient $\mu(z)=(z,Az)/|z|^2$:
--
--   $$a_i=\frac{|r_i|^2}{(p_i,Ap_i)}=\frac{(p_i,r_i)}{(p_i,Ap_i)}=\frac{(p_i,r_0)}{(p_i,Ap_i)}, \tag{5:10}$$
--
--   $$b_i=\frac{|r_{i+1}|^2}{|r_i|^2}=-\frac{(r_{i+1},Ap_i)}{(p_i,Ap_i)}=-\frac{(r_{i+1},Ar_i)}{(p_i,Ap_i)}, \tag{5:11}$$
--
--   $$\frac1{a_0}=\mu(r_0),\qquad \mu(p_i)<\frac1{a_i}<\mu(r_i)\quad(0<i<m). \tag{5:12}$$
--
--   For every active step $i<m$, $1/a_i$ lies between the smallest and the largest eigenvalue of $A$.
--
--   The formulas give alternative, numerically different ways of computing the cg scalars (§8 uses them), and (5:12) brackets the step length by Rayleigh quotients and the spectrum.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - reading: strict bounds (5:12) “for $i>0$” → for $0<i<m$; reason: after termination $p_i=r_i=0$ and there is no Rayleigh quotient to compare; the paper's proof uses $|r_i|<|p_i|$, valid for active steps
--   - reading: “lies between the smallest and largest characteristic roots” → $\lambda_{\min}\le1/a_i\le\lambda_{\max}$ for $i<m$, via the eigenvalues of the Hermitian matrix $A$; reason: non-strict bracketing, as the sentence states; equality occurs, e.g. $r_0$ an eigenvector
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 416, Theorem 5:5, eqs. (5:10)–(5:12) (PDF p. 8)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:5 (Hestenes–Stiefel 1952, p. 416): the formulas (5:10), (5:11), the bounds (5:12)
and the eigenvalue bracket for `1/aᵢ`; `m` is the step at which the cg-method terminates. -/
theorem theorem_5_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ,
      cgAlpha A (cgIter A k x₀ i) = ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgAlpha A (cgIter A k x₀ i) = ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).r) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgAlpha A (cgIter A k x₀ i) = ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ 0).r) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p))) ∧
    (∀ i : ℕ,
      cgBeta A k x₀ i = ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
        ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgBeta A k x₀ i = -((cgIter A k x₀ (i + 1)).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgBeta A k x₀ i = -((cgIter A k x₀ (i + 1)).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).r)) /
        ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p))) ∧
    1 / cgAlpha A (cgIter A k x₀ 0) = rayleigh A (cgIter A k x₀ 0).r ∧
    (∀ i : ℕ, 0 < i → i < m →
      rayleigh A (cgIter A k x₀ i).p < 1 / cgAlpha A (cgIter A k x₀ i) ∧
        1 / cgAlpha A (cgIter A k x₀ i) < rayleigh A (cgIter A k x₀ i).r) ∧
    (∀ i : ℕ, i < m → ∃ j₁ j₂ : Fin n,
      hA.1.eigenvalues j₁ ≤ 1 / cgAlpha A (cgIter A k x₀ i) ∧
        1 / cgAlpha A (cgIter A k x₀ i) ≤ hA.1.eigenvalues j₂) := by sorry

end ConjGrad.ErrorDecrease.Supplement
