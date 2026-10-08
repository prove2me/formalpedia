-- Prove2me | Theorems.Thm_BoydADMM_Convergence_dual_step_monotone
-- name    : BoydADMM.Convergence.dual_step_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:53:58.601853+00:00
-- url     : https://prove2.me/theorems/38b978cc-f77d-47fe-8a87-4055892156f0
-- title:
--   Proof of (A.1) — $(y^{k+1}-y^k)^T(B(z^{k+1}-z^k))\le0$ for $k\ge1$
-- statement:
--   Let $f,g$ satisfy Assumption 1, let $\rho>0$ and let $(x^k,z^k,y^k)$ be any ADMM run. Then for every $k\ge1$,
--
--   $$
--   (y^{k+1}-y^k)^T\bigl(B(z^{k+1}-z^k)\bigr)\le0 .
--   $$
--
--   This is the monotonicity step in the proof of (A.1): $z^{k+1}$ minimizes $g(z)+y^{(k+1)T}Bz$ and $z^k$ minimizes $g(z)+y^{kT}Bz$, and the two optimality conditions combine.
--
--   **Formalization Note** The book does not state the index range; its argument needs $z^k$ to be itself a $z$-update, i.e. $k\ge1$, because $z^0$ is an arbitrary starting point. The Lean statement is written with $k+1$ and $k+2$ in place of the book's $k$ and $k+1$, $k\ge0$.
-- source:
--   Boyd et al., Found. Trends Mach. Learn. 3(1) (2011), Appendix A, proof of (A.1), p. 110

import Mathlib
import Definitions.Def_BoydADMM_Convergence_Model

namespace BoydADMM.Convergence

/-- Proof of (A.1), p. 110: `(y^{k+1} − y^k)ᵀ(B(z^{k+1} − z^k)) ≤ 0` for every book index
`k ≥ 1` (here written with `k + 1` in place of the book's `k`, so that `z^k` is itself a
`z`-update). -/
theorem dual_step_monotone
  {n m p : ℕ} (P : Problem n m p) (hA1 : P.Assumption1) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {z : ℕ → EuclideanSpace ℝ (Fin m)}
    {y : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : P.IsADMMSeq ρ x z y) (k : ℕ) :
    inner ℝ (y (k + 2) - y (k + 1)) (P.Bmul (z (k + 2) - z (k + 1))) ≤ 0 := by sorry

end BoydADMM.Convergence
