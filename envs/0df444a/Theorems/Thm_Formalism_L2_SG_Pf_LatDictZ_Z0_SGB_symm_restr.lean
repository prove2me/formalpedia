-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_symm_restr
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.symm_restr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:57:43.454629+00:00
-- url     : https://prove2.me/theorems/4e02f35c-66de-43ba-a5df-48a7eca57397
-- title:
--   SGB: symm restr
-- statement:
--   The SGB construction uses the symm restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L154-L158

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.symm_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hsy : h.IsSymm) (W : Submodule K V) :
    (restr h W).IsSymm := by sorry
