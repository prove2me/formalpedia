-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_6_1
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:57:27.920625+00:00
-- url     : https://prove2.me/theorems/28a9f8ff-7699-4bc4-a537-b743befe875b
-- title:
--   Theorem 6:1 — distinct estimates, minimization on $P_i$, (6:1)–(6:2) and the expansions (6:3)
-- statement:
--   Let $x_0,x_1,\dots,x_m=h$ be the estimates of the cg-method for a real symmetric positive definite $A$, $f(x)=(h-x,A(h-x))$, $\mu$ the Rayleigh quotient. Then
--
--   1. $x_0,x_1,\dots,x_m$ are distinct;
--   2. $x_i$ minimizes $f$ on the $i$-dimensional plane $P_i=x_0+\operatorname{span}(p_0,\dots,p_{i-1})$ passing through $x_0,\dots,x_i$ ($p_0,\dots,p_{i-1}$ are linearly independent for $i\le m$);
--   3. $$f(x_{i-1})-f(x_i)=a_{i-1}|r_{i-1}|^2=\mu(p_{i-1})|x_{i-1}-x_i|^2, \tag{6:1}$$
--   $$f(x_i)-f(x_j)=a_i|r_i|^2+\cdots+a_{j-1}|r_{j-1}|^2\quad(i<j); \tag{6:2}$$
--   4. $$x_i=x_0+\sum_{j=0}^{i-1}a_jp_j=x_0+\sum_{j=0}^{i-1}\frac{f(x_j)-f(x_i)}{|r_j|^2}\,r_j . \tag{6:3}$$
--
--   This is the restatement of Theorem 4:3 for the cg-method together with explicit formulas for the estimates; (6:1) and (6:2) are also the published base items `error_step_6_1` and `error_diff_6_2`.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 416, Theorem 6:1, eqs. (6:1)–(6:3) (PDF p. 8)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 6:1 (Hestenes–Stiefel 1952, p. 416): distinct estimates up to termination, minimization
of `f` on the plane `Pᵢ`, (6:1), (6:2) and both expansions (6:3); `m` is the step at which the
cg-method terminates. -/
theorem theorem_6_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i j : ℕ, i ≤ m → j ≤ m → i ≠ j → (cgIter A k x₀ i).x ≠ (cgIter A k x₀ j).x) ∧
    (∀ i : ℕ, (cgIter A k x₀ i).x ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i ∧
      ∀ y ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i,
        errorFun A h (cgIter A k x₀ i).x ≤ errorFun A h y) ∧
    (∀ i : ℕ, ∀ j ≤ i, (cgIter A k x₀ j).x ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i) ∧
    (∀ i ≤ m, LinearIndependent ℝ (fun j : Fin i => (cgIter A k x₀ j).p)) ∧
    (∀ i : ℕ,
      errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ (i + 1)).x =
        cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ∧
      cgAlpha A (cgIter A k x₀ i) * ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        rayleigh A (cgIter A k x₀ i).p *
          (((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x) ⬝ᵥ
            ((cgIter A k x₀ i).x - (cgIter A k x₀ (i + 1)).x))) ∧
    (∀ i j : ℕ, i < j →
      errorFun A h (cgIter A k x₀ i).x - errorFun A h (cgIter A k x₀ j).x =
        ∑ l ∈ Finset.Ico i j,
          cgAlpha A (cgIter A k x₀ l) * ((cgIter A k x₀ l).r ⬝ᵥ (cgIter A k x₀ l).r)) ∧
    (∀ i : ℕ,
      (cgIter A k x₀ i).x = x₀ + ∑ j ∈ Finset.range i,
        cgAlpha A (cgIter A k x₀ j) • (cgIter A k x₀ j).p ∧
      (cgIter A k x₀ i).x = x₀ + ∑ j ∈ Finset.range i,
        ((errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ i).x) /
          ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r)) • (cgIter A k x₀ j).r) := by sorry

end ConjGrad.ErrorDecrease.Supplement
