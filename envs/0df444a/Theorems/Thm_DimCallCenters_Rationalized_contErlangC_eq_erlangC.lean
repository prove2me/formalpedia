-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_contErlangC_eq_erlangC
-- name    : DimCallCenters.Rationalized.contErlangC_eq_erlangC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:25:49.42199+00:00
-- url     : https://prove2.me/theorems/52f59e32-cec7-453a-8856-5d93a1ef9f71
-- title:
--   Section 3, p. 12 — $H(N,\nu) = \pi(N,\nu)$ at integer $N$
-- statement:
--   Let $N \ge 1$ be an integer and $0 < \nu < N$. Then the continuous extension agrees with the Erlang-C formula:
--
--   $$H(N,\nu) = \pi(N,\nu).$$
--
--   Consequently $\pi_\lambda(x) = \pi(N_\lambda(x),\lambda/\mu)$ whenever $N_\lambda(x)$ is an integer, which links the continuous cost $C_\lambda$ to the discrete cost $C(N,\lambda)$: $C_\lambda(x) = C(N_\lambda(x),\lambda) - F(\lambda/\mu)$ at such $x$.
--
--   **Formalization Note** The paper states this claim without number, citing its references [9], [10]; the hypothesis $\nu < N$ is the stability condition under which both sides are the probability of waiting.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, unnumbered claim 'pi_lambda(x) = pi(N_lambda(x), lambda/mu) for integer values of N_lambda(x)'

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_contErlangC

namespace DimCallCenters.Rationalized

/-- Section 3, p. 12: at an integer number of servers `N` with `0 < ν < N`, the continuous
extension `H(N, ν)` coincides with the Erlang-C formula `π(N, ν)`; hence
`π_λ(x) = π(N_λ(x), λ/μ)` whenever `N_λ(x)` is an integer. -/
theorem contErlangC_eq_erlangC (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hνN : ν < N) :
    contErlangC N ν = erlangC N ν := by sorry

end DimCallCenters.Rationalized
