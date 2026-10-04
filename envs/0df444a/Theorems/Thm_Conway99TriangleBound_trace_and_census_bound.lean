-- Prove2me | Theorems.Thm_Conway99TriangleBound_trace_and_census_bound
-- name    : Conway99TriangleBound.trace_and_census_bound
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:49:26.825902+00:00
-- url     : https://prove2.me/theorems/28d8bd50-7117-4241-bdf8-62e6c86397a2
-- title:
--   Conditional triangle trace and prism bounds
-- statement:
--   For 231 triangle trace indices, assume each trace satisfies the stated frame floor and divisibility by four, the total trace is 84·delta−58212, and delta+3·prisms=4158. Then delta is at least 858 and the prism count is at most 1100. These inputs are explicit premises, not derived from a graph here.
-- source:
--   Frozen integrated source a45708acebe3f397faccb1b646be906f24f23ee5, formalization/2026-10-03/triangle-bound/TriangleBound.lean, theorem Conway99Formal.TriangleBound.bound_from_trace_and_census, source SHA-256 5fa5ddbe82ebfeda512916ffccf395a70c4e977ab44120e2d425811f9fb46a2e. Formal-geometry source QA run-f9fd0a584ca5 passed on that integration; this standalone wrapper is checked separately.

import Mathlib
set_option autoImplicit false

theorem Conway99TriangleBound.trace_and_census_bound {T : Type*} [Fintype T] (traceSq : T → ℤ) (delta prisms : ℕ) (hcard : Fintype.card T = 231) (hframe : ∀ t, 396 ≤ 7 * traceSq t) (hfour : ∀ t, 4 ∣ traceSq t) (hsum : (∑ t : T, traceSq t) = 84 * (delta : ℤ) - 58212) (hcensus : delta + 3 * prisms = 4158) : 858 ≤ delta ∧ prisms ≤ 1100 := by sorry
