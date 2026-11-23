-- Prove2me | Theorems.Thm_Folding_implies_BadEvent
-- name    : Folding_implies_BadEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:31:11.426807+00:00
-- url     : https://prove2.me/theorems/f4bd83c1-373c-4df0-8f4e-a260f8fd076e
-- title:
--   Folding implies Bad Event: Folding implies Bad Event
-- statement:
--   The Folding implies Bad Event construction uses the Folding implies Bad Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L258-L268
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean#L258-L268

import Definitions.Def_SimpleRbrFri_State
import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem Folding_implies_BadEvent {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (m : ℕ) (d : ℕ) (hm : m > 0) (hd : d ≥ m)
    (f : F → F) (delta : ℝ) (r : F)
    (h_event : FoldingBadEvent D m (reedSolomon D d)
      (reedSolomon (pow_domain D m) (d / m)) f delta r) :
    let L := pow_domain D m
    let C1 := reedSolomon L (d / m)
    let f_i := folding_components D m f
    let vec_r := fun i : Fin m ↦ r ^ (i : ℕ)
    BadEvent C1 m f_i delta vec_r := by sorry
