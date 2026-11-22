-- Prove2me | Theorems.Thm_Comp_CsgQ_castIcc_coe
-- name    : Comp.CsgQ.castIcc_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:41.7178+00:00
-- url     : https://prove2.me/theorems/ae84e269-9ac5-4ad9-8339-046695d84ff2
-- title:
--   Csg Q: cast Icc coe
-- statement:
--   The Csg Q construction uses the cast Icc coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L94-L95
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean#L94-L95

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S : Type*}

theorem Comp.CsgQ.castIcc_coe (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (s : S) :
    ((castIcc v h0 h1 s : ℝ)) = ((v s : ℚ) : ℝ) := by sorry

attribute [defeq] Comp.CsgQ.castIcc_coe
