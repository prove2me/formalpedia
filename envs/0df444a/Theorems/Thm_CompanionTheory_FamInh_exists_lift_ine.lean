-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_exists_lift_ine
-- name    : CompanionTheory.FamInh.exists_lift_ine
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:19.656964+00:00
-- url     : https://prove2.me/theorems/29086126-20c4-5a50-b459-ddbc3366b911
-- title:
--   Fam Inh: exists lift ine
-- statement:
--   The Fam Inh construction uses the exists lift ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L119-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L119-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open CompanionTheory CompanionTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

theorem CompanionTheory.FamInh.exists_lift_ine (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L} (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L)) :
    ∃ σ ∈ Ine (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by sorry
