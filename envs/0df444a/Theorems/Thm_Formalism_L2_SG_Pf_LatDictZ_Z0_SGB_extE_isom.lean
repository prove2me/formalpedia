-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_extE_isom
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.extE_isom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:58:20.070805+00:00
-- url     : https://prove2.me/theorems/c6ac07f6-7fa3-4228-8cef-44ac04224d5e
-- title:
--   SGB: ext E isom
-- statement:
--   The SGB construction uses the ext E isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L99-L104

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.extE_isom (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0) (hs : ∀ u v, star (h u v) = h v u)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X))
    (hg : ∀ u v, h (g u : V) (g v : V) = h (u : V) (v : V)) (x y : V) :
    h (extE h X hX g x) (extE h X hX g y) = h x y := by sorry
