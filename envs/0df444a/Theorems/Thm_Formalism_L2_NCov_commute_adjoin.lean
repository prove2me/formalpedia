-- Prove2me | Theorems.Thm_Formalism_L2_NCov_commute_adjoin
-- name    : Formalism.L2.NCov.commute_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:56:10.590325+00:00
-- url     : https://prove2.me/theorems/33f14d80-bf51-4eb5-b615-9a886cfe783e
-- title:
--   NCov: commute adjoin
-- statement:
--   The NCov construction uses the commute adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L128-L131

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}

theorem Formalism.L2.NCov.commute_adjoin (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {a b : End K V}
    (ha : a ∈ Algebra.adjoin O S) (hb : b ∈ Algebra.adjoin O S) : Commute a b := by sorry
