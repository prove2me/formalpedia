-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_body_degree
-- name    : DetDLP.m3b_ec_body_degree
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T21:31:00.741374+00:00
-- url     : https://prove2.me/theorems/379d14b3-d7a2-441f-9334-2ebbe63403fe
-- title:
--   Degree of every named gate in the native EC arithmetic body
-- statement:
--   Each named gate in the EC arithmetic, address bus, and prefix body has arity bounded by the explicit sublinear multiplier degree cap.
-- source:
--   Supporting lemma for DetDLP.w3_ec_native_wire_programs, Section 4.2 (pp. 14–15).

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
open DetDLP DetDLP.M3B

theorem DetDLP.m3b_ec_body_degree {p m k : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) (T : ℕ) (P : E.toAffine.Point) (pre : List Bool) :
    ∀ j, S8J.degreeOf (ECPhysicalNet.body (k:=k) E seed T P pre).core.A.gate j ≤ max 12 ⌈136*((bitLen p:ℝ)+2)^((3:ℝ)/4)⌉₊ := by sorry
