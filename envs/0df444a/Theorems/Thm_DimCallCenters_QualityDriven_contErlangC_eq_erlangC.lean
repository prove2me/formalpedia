-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_contErlangC_eq_erlangC
-- name    : DimCallCenters.QualityDriven.contErlangC_eq_erlangC
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:55:59.557987+00:00
-- url     : https://prove2.me/theorems/543a6660-ca47-4983-91f4-bfd692102eb3
-- title:
--   Section 3, p. 12 — $H(N,\nu) = \pi(N,\nu)$ at integer $N$
-- statement:
--   Let $N$ be a positive integer and $0 < \nu < N$. Then the continuous extension of the Erlang-C formula agrees with the Erlang-C formula:
--
--   $$
--   H(N,\nu) = \left\{\nu\int_0^\infty e^{-\nu t}\,t\,(1+t)^{N-1}\,dt\right\}^{-1} = \pi(N,\nu).
--   $$
--
--   Consequently $\pi_\lambda(x) = \pi(N_\lambda(x),\lambda/\mu)$ whenever $N_\lambda(x)$ is an integer, and $C_\lambda(x) = C(N_\lambda(x),\lambda) - F(\lambda/\mu)$ there. The paper cites this identity ([9], [10]) and uses it to pass between the discrete and the continuous staffing problems.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, the claim $\pi_\lambda(x) = \pi(N_\lambda(x), \lambda/\mu)$ for integer $N_\lambda(x)$

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_contErlangC

namespace DimCallCenters.QualityDriven

/-- Section 3, p. 12: at an integer number of DimCallCenters.Rationalized.servers `N` with `0 < ν < N`, the continuous
extension `H(N, ν)` coincides with the Erlang-C formula `π(N, ν)`; hence
`π_λ(x) = π(N_λ(x), λ/μ)` whenever `N_λ(x)` is an integer. -/
theorem contErlangC_eq_erlangC (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hνN : ν < N) :
    DimCallCenters.Rationalized.contErlangC N ν = DimCallCenters.Rationalized.erlangC N ν := by sorry

end DimCallCenters.QualityDriven
