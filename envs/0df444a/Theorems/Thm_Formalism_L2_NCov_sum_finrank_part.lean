-- Prove2me | Theorems.Thm_Formalism_L2_NCov_sum_finrank_part
-- name    : Formalism.L2.NCov.sum_finrank_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:34.159491+00:00
-- url     : https://prove2.me/theorems/bb811b9b-d6d8-4da1-95cd-a3ee5a673ce8
-- title:
--   NCov: sum finrank part
-- statement:
--   The NCov construction uses the sum finrank part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L233-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L233-L252

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

theorem Formalism.L2.NCov.sum_finrank_part [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (Ms : Finset (Ideal (Algebra.adjoin O S)))
    (hMs : ∀ 𝔪 : Ideal (Algebra.adjoin O S), 𝔪.IsMaximal → 𝔪 ∈ Ms) :
    ∑ 𝔪 ∈ Ms, finrank K (part (Algebra.adjoin O S) 𝔪) = finrank K V := by sorry
