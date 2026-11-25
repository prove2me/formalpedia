-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_inertia_eq_bot_iff
-- name    : CompanionTheory.FamInh.inertia_eq_bot_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:38.213871+00:00
-- url     : https://prove2.me/theorems/43dca28a-acbd-49fa-8af2-4115c47bd2ae
-- title:
--   Fam Inh: inertia eq bot iff
-- statement:
--   The Fam Inh construction uses the inertia eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinA.lean#L166-L172

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
omit [IsAlgClosure K Ω] [IsAlgClosure L Ω]

theorem CompanionTheory.FamInh.inertia_eq_bot_iff (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ ↔ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by sorry
