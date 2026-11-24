-- Prove2me | Theorems.Thm_Formalism_L2_NCov_iSup_W_eq_top
-- name    : Formalism.L2.NCov.iSup_W_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.671856+00:00
-- url     : https://prove2.me/theorems/b3372e29-7c7c-4aad-b8be-41fb5399565f
-- title:
--   NCov: i Sup W eq top
-- statement:
--   The NCov construction uses the i Sup W eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L211-L215

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

theorem Formalism.L2.NCov.iSup_W_eq_top [FiniteDimensional K V] (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) : ⨆ χ, W (Algebra.adjoin O S) χ = ⊤ := by sorry
