-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_piLam_eq_erlangC
-- name    : DimCallCenters.Constraint.piLam_eq_erlangC
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:57:56.306574+00:00
-- url     : https://prove2.me/theorems/ab091a2a-dd24-4376-9970-2bc0f2bc1ee5
-- title:
--   Section 3: π_λ(x) equals the Erlang-C formula at integer staffing levels
-- statement:
--   Let $\mu, \lambda, x > 0$ and suppose that $N_\lambda(x) = \lambda/\mu + x\sqrt{\lambda/\mu}$ is an integer $N$. Then
--
--   $$\pi_\lambda(x) = \pi\big(N_\lambda(x), \lambda/\mu\big),$$
--
--   i.e. the continuous Erlang-C function $H(N, \lambda/\mu)$ agrees with the Erlang-C probability of waiting $\pi(N, \lambda/\mu)$.
--
--   The identity justifies $\pi_\lambda$ as the continuous extension of the Erlang-C formula: the continuous waiting cost $K_\lambda(x)$ equals the waiting cost $K(N,\lambda)$ at integer staffing levels.
--
--   **Formalization Note** The positivity of $x$ makes $N > \lambda/\mu$, the range in which the Erlang-C formula has its probabilistic meaning.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, the claim π_λ(x) = π(N_λ(x), λ/μ) for integer N_λ(x) (citing [9], [10])

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_piLam

namespace DimCallCenters.Constraint

/-- Section 3, p. 12: `π_λ(x) = π(N_λ(x), λ/μ)` whenever the staffing level `N_λ(x)` is an
integer (here for `μ, λ, x > 0`, so that `N_λ(x) > λ/μ`). -/
theorem piLam_eq_erlangC (μ lam x : ℝ) (hμ : 0 < μ) (hlam : 0 < lam) (hx : 0 < x) (N : ℕ)
    (hN : DimCallCenters.Rationalized.servers μ lam x = (N : ℝ)) :
    DimCallCenters.Rationalized.piLam μ lam x = DimCallCenters.Rationalized.erlangC N (lam / μ) := by sorry

end DimCallCenters.Constraint
