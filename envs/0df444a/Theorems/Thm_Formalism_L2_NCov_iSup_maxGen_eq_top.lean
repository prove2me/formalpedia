-- Prove2me | Theorems.Thm_Formalism_L2_NCov_iSup_maxGen_eq_top
-- name    : Formalism.L2.NCov.iSup_maxGen_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:54.57968+00:00
-- url     : https://prove2.me/theorems/084ddf47-c2e3-4b61-b30c-301c092d38bb
-- title:
--   NCov: i Sup max Gen eq top
-- statement:
--   The NCov construction uses the i Sup max Gen eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L186-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L186-L209

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

theorem Formalism.L2.NCov.iSup_maxGen_eq_top [FiniteDimensional K V] (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) (t : Algebra.adjoin O S) :
    ⨆ μ, (t : End K V).maxGenEigenspace μ = ⊤ := by sorry
