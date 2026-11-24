-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_extE_apply
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.extE_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:24.871488+00:00
-- url     : https://prove2.me/theorems/131c2756-21fa-4404-9c77-8e9172bfa9eb
-- title:
--   SGB: ext E apply
-- statement:
--   The SGB construction uses the ext E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L82-L84

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.extE_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V) (hX : h X X ≠ 0)
    (g : LinearMap.ker (h X) ≃ₗ[K] LinearMap.ker (h X)) (x : V) :
    extE h X hX g x = ext h X hX g x := by sorry
