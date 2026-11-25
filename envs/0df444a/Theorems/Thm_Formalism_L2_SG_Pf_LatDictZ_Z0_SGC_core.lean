-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGC_core
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.core
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:57:46.473441+00:00
-- url     : https://prove2.me/theorems/fef98782-7a3c-4a57-b4cd-99f9ad181bc5
-- title:
--   SGC: core
-- statement:
--   The SGC construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SemiGenusLocal.lean#L39-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SemiGenusLocal.lean#L39-L83

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SemiGenusLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGC
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.core {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V], finrank K V = n →
    ∀ (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ M₁ M₂ : AddSubgroup V, IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      ∃ g : V ≃ₗ[K] V, (∀ x y, h (g x) (g y) = h x y) ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by sorry
