-- Prove2me | Theorems.Thm_Comp_CsgQ_G_le_coe_iter
-- name    : Comp.CsgQ.G_le_coe_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:06:51.232285+00:00
-- url     : https://prove2.me/theorems/24f71429-bacd-4115-a175-fad42efa7cd8
-- title:
--   Csg Q: G le coe iter
-- statement:
--   Every stage of the computed descent from `Finset.univ` is an upper bound on `G safe`. One
--       `OrderHom.gfp_le_of_step` per step, with `coe_gStepF` and `GOrderHom_toCSG` identifying the
--       computed step with the specification's own operator at each stage.
--
--       This is the half that the iteration -- not a certificate -- has to supply. The other half,
--       `G safe`'s *lower* bound, comes free from the fixed-point check, which is the asymmetry
--       `Comp/Reach.lean` and `Csg/IntervalCertificate.lean` both turn on.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L108-L119
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L108-L119

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.G_le_coe_iter (G : CsgQ S A1 A2) (h : G.WellFormed) (safe : Finset S) (n : ℕ) :
    (G.toCSG h).G (↑safe : Set S) ≤ ↑((G.gStepF safe)^[n] Finset.univ) := by sorry
