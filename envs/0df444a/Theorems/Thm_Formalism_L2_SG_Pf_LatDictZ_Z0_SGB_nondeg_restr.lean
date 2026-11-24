-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_nondeg_restr
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.nondeg_restr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:57:05.842809+00:00
-- url     : https://prove2.me/theorems/ee259493-b13b-411b-bfa1-9fd7238b1b7f
-- title:
--   SGB: nondeg restr
-- statement:
--   The SGB construction uses the nondeg restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L147-L152

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
variable {S : Subring K}

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.nondeg_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {X : V} (hX : h X X ≠ 0) (w : LinearMap.ker (h X))
    (hw : ∀ y, restr h (LinearMap.ker (h X)) w y = 0) : w = 0 := by sorry
