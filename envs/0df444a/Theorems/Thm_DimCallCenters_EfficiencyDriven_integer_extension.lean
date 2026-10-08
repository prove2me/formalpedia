-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_integer_extension
-- name    : DimCallCenters.EfficiencyDriven.integer_extension
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:13.408041+00:00
-- url     : https://prove2.me/theorems/55614631-cad3-49a9-b6b0-7eccd2ff902b
-- title:
--   Section 3 — continuous Erlang-C agrees at integers
-- statement:
--   For a positive offered load $\nu$ and a stable integer server count $N>\nu$, the continuous Erlang-C extension $H$ equals the finite-sum Erlang-C probability:
--
--   $$
--   H(N,\nu)=\pi(N,\nu).
--   $$
--
--   The identity makes the continuous objective agree with the queueing cost at integer staffing levels. It is the unnumbered claim immediately after the definition of $H$ on printed page 12.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 12, Section 3, identity following the definition of H

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_erlangC
import Definitions.Def_DimCallCenters_Rationalized_contErlangC

namespace DimCallCenters.EfficiencyDriven

/-- Section 3, p. 12: the continuous extension agrees with Erlang-C
at stable integer staffing levels. -/
theorem integer_extension (ν : ℝ) (N : ℕ) (hν : 0 < ν)
    (hstable : ν < (N : ℝ)) :
    DimCallCenters.Rationalized.contErlangC N ν = DimCallCenters.Rationalized.erlangC N ν := by sorry

end DimCallCenters.EfficiencyDriven
