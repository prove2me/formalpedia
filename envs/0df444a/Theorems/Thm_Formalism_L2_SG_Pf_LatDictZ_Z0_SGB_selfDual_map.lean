-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_selfDual_map
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.selfDual_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:58:17.834704+00:00
-- url     : https://prove2.me/theorems/7938fbe7-d976-431e-9cc4-dfac3e5ab5fe
-- title:
--   SGB: self Dual map
-- statement:
--   The SGB construction uses the self Dual map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L160-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L160-L179

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.selfDual_map {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V} (hM : IsSelfDualMod S h M)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, h (g x) (g y) = h x y) :
    IsSelfDualMod S h (M.comap (g.symm : V →ₗ[K] V).toAddMonoidHom) := by sorry
