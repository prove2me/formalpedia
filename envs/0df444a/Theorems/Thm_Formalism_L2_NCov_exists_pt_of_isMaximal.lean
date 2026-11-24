-- Prove2me | Theorems.Thm_Formalism_L2_NCov_exists_pt_of_isMaximal
-- name    : Formalism.L2.NCov.exists_pt_of_isMaximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:37.70785+00:00
-- url     : https://prove2.me/theorems/72fb52f2-7c6e-451b-8778-6a3662115b85
-- title:
--   NCov: exists pt of is Maximal
-- statement:
--   The NCov construction uses the exists pt of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L334-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L334-L402

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
set_option linter.deprecated false

theorem Formalism.L2.NCov.exists_pt_of_isMaximal [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (𝔪 : Ideal (Algebra.adjoin O S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ ψ : Algebra.adjoin O S →ₐ[O] O, W _ (pt ψ) ≠ ⊥ ∧ cls ψ = 𝔪 := by sorry
