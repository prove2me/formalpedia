-- Prove2me | Theorems.Thm_ChromaticReconstruction_toFinsupp_pair_sub
-- name    : ChromaticReconstruction.toFinsupp_pair_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:20:18.105292+00:00
-- url     : https://prove2.me/theorems/f7ca66d4-babb-4cb5-b60f-c269ae02419b
-- title:
--   Chromatic Reconstruction: to Finsupp pair sub
-- statement:
--   The Chromatic Reconstruction construction uses the to Finsupp pair sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L27-L31
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L27-L31

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]

theorem ChromaticReconstruction.toFinsupp_pair_sub (s : ℕ) :
    Multiset.toFinsupp (2 ::ₘ Multiset.replicate s 1) - Finsupp.single 2 1 =
      Multiset.toFinsupp (Multiset.replicate s 1) := by sorry
