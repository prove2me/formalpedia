-- Prove2me | Theorems.Thm_EulerMascheroni_P2_phase_noncancellation
-- name    : EulerMascheroni.P2.phase_noncancellation
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T00:09:59.67703+00:00
-- url     : https://prove2.me/theorems/12d57034-9682-4ad6-a314-beba61cf6307
-- title:
--   Recurring noncancellation of the fifth-root saddle phase
-- statement:
--   The explicitly defined phase has sine of absolute value at least one half for infinitely many indices. This now has an accepted Lean proof: the phase tends to infinity, its successive increments tend to zero, and a first-crossing argument finds indices near arbitrarily distant sine maxima. This is a classical argument and no novelty is claimed for it. It discharges the phase child of the [sharp-rate sketch](p2m:theorem/49746242-9b3e-4277-b5a4-6d00d752b173) and supplies a hypothesis of the [conditional irrationality bridge](p2m:theorem/577d6ca7-de66-47f3-9ab9-318ce5d0fe5e).
-- source:
--   Explicit family: Van Assche–Wolfs, https://arxiv.org/html/2404.09799v3, section 5. Proposed p=2 refinement: local SADDLE_DRAFT.md, 11 September 2026. Proof-under-review research target; NOT attributed to an established theorem in the source.

import Definitions.Def_eulerMascheroni_p2Approximation
open Filter Topology
open EulerMascheroni.P2

theorem EulerMascheroni.P2.phase_noncancellation : ∃ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ |Real.sin (phase (n+1))| := by sorry
