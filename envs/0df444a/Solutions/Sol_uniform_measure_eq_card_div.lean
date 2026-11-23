-- Prove2me | solution 1 for uniform_measure_eq_card_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:30.277499+00:00
-- url     : https://prove2.me/submissions/4fca343c-af9b-458b-922e-6d62085edf08

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [Field F] [DecidableEq F]
theorem _root_.solution [Fintype F] [MeasurableSpace F] [DiscreteMeasurableSpace F]
    [Nonempty F] (S : Set F) [DecidablePred (· ∈ S)] :
    (PMF.uniformOfFintype F).toMeasure S = (Finset.univ.filter (· ∈ S)).card / Fintype.card F := by
  simp [PMF.toMeasure_uniformOfFintype_apply S .of_discrete]
