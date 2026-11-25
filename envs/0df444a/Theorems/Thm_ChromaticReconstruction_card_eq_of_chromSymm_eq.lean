-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_eq_of_chromSymm_eq
-- name    : ChromaticReconstruction.card_eq_of_chromSymm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:24:14.09411+00:00
-- url     : https://prove2.me/theorems/61c75970-88c5-41c8-a9eb-c2f5d32016f2
-- title:
--   Chromatic Reconstruction: card eq of chrom Symm eq
-- statement:
--   The Chromatic Reconstruction construction uses the card eq of chrom Symm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L52-L58
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L52-L58

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]

theorem ChromaticReconstruction.card_eq_of_chromSymm_eq {G : SimpleGraph V} {H : SimpleGraph W}
    (h : chromSymm G = chromSymm H) : Fintype.card V = Fintype.card W := by sorry
