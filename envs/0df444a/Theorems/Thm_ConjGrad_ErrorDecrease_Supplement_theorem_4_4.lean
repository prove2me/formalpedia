-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_4_4
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:54:11.868561+00:00
-- url     : https://prove2.me/theorems/abd362a5-99df-4c45-b1ec-e97b31b0b4c1
-- title:
--   Theorem 4:4 — residual, error-function and error-vector bounds via Rayleigh quotients
-- statement:
--   Let $A$ be a real symmetric positive definite matrix, $h$ the solution of $Ah=k$, and $\mu(z)=(z,Az)/|z|^2$ the Rayleigh quotient (4:12). For every estimate $x$, with error vector $y=h-x$, residual $r=k-Ax$ and error function $f(x)=(y,Ay)$,
--
--   $$\frac{|r|^2}{\mu(r)}\le f(x)\le\frac{|r|^2}{\mu(y)},\qquad \mu(y)\le\mu(r),\qquad \frac{|r|}{\mu(r)}\le|y|\le\frac{|r|}{\mu(y)} . \tag{4:11, 4:13, 4:14}$$
--
--   The bounds convert the computable residual $r$ into two-sided estimates of the error function and of the length of the error vector.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; $|z|=\sqrt{(z,z)}$ and $\mu$ is the published `rayleigh` (with $\mu(0)=0$). $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption.
--
--   Differences from the source:
--   - encoding: the quotients for an estimate $x\neq h$ → every $x$, with $\mu(0)=0$ and $t/0=0$ so that at $x=h$ all members are $0$; reason: at $x=h$ the source's quantities are undefined or zero; for $x\neq h$ the statement is the source's
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 413, Theorem 4:4, eqs. (4:11)–(4:14) (PDF p. 5)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 4:4 (Hestenes–Stiefel 1952, p. 413): for every estimate `x`, with error vector
`y = h − x` and residual `r = k − Ax`, the bounds (4:11), (4:13) and (4:14). -/
theorem theorem_4_4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x : Fin n → ℝ) :
    ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (k - A *ᵥ x) ≤ errorFun A h x ∧
    errorFun A h x ≤ ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (h - x) ∧
    rayleigh A (h - x) ≤ rayleigh A (k - A *ᵥ x) ∧
    Real.sqrt ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (k - A *ᵥ x) ≤
      Real.sqrt ((h - x) ⬝ᵥ (h - x)) ∧
    Real.sqrt ((h - x) ⬝ᵥ (h - x)) ≤
      Real.sqrt ((k - A *ᵥ x) ⬝ᵥ (k - A *ᵥ x)) / rayleigh A (h - x) := by sorry

end ConjGrad.ErrorDecrease.Supplement
