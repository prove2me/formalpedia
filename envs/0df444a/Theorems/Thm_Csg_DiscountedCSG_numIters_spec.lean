-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_numIters_spec
-- name    : Csg.DiscountedCSG.numIters_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:32:41.820336+00:00
-- url     : https://prove2.me/theorems/5e598f1b-8a2e-417e-91dc-87e58f6530ad
-- title:
--   Discounted CSG: num Iters spec
-- statement:
--   The Discounted CSG construction uses the num Iters spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L148-L150
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/DiscountedValueIteration.lean#L148-L150

import Definitions.Def_Csg_Discounted
import Definitions.Def_Csg_DiscountedValueIteration
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.numIters_spec {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    D.stopCond eps v (D.numIters heps v) := by sorry
