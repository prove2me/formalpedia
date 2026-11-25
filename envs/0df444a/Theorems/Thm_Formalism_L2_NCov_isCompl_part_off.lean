-- Prove2me | Theorems.Thm_Formalism_L2_NCov_isCompl_part_off
-- name    : Formalism.L2.NCov.isCompl_part_off
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:19.301172+00:00
-- url     : https://prove2.me/theorems/aa3150c7-5561-4db5-b60e-e407581d0e4e
-- title:
--   NCov: is Compl part off
-- statement:
--   The NCov construction uses the is Compl part off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L404-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L404-L425

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
open Polynomial
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}

theorem Formalism.L2.NCov.isCompl_part_off [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (𝔪 : Ideal (Algebra.adjoin O S)) :
    IsCompl (part (Algebra.adjoin O S) 𝔪) (off (Algebra.adjoin O S) 𝔪) := by sorry
