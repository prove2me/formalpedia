-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGC_exists_isom_vec
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.exists_isom_vec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:58:41.660037+00:00
-- url     : https://prove2.me/theorems/4de619fb-61a1-4d0f-8b96-eab8e760631a
-- title:
--   SGC: exists isom vec
-- statement:
--   The SGC construction uses the exists isom vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SemiGenusLocal.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SemiGenusLocal.lean#L14-L37

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGC.exists_isom_vec {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {e X : V}
    (he : h e e ≠ 0) (hXe : h X X = h e e) :
    ∃ τ : V ≃ₗ[K] V, (∀ x y, h (τ x) (τ y) = h x y) ∧ τ e = X := by sorry
