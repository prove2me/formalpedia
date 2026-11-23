-- Prove2me | Theorems.Thm_Formalism_L2_NCov_exists_pt
-- name    : Formalism.L2.NCov.exists_pt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:16.813811+00:00
-- url     : https://prove2.me/theorems/cf262de4-997e-461a-80ca-d6d90ba83a23
-- title:
--   NCov: exists pt
-- statement:
--   The NCov construction uses the exists pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L167-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L167-L180

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

theorem Formalism.L2.NCov.exists_pt (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (hinj : Function.Injective (algebraMap O K))
    {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) :
    ∃ ψ : Algebra.adjoin O S →ₐ[O] O, pt ψ = χ := by sorry
