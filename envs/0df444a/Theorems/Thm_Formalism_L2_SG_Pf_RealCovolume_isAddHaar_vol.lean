-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_isAddHaar_vol
-- name    : Formalism.L2.SG.Pf.RealCovolume.isAddHaar_vol
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:04.745808+00:00
-- url     : https://prove2.me/theorems/6039d49b-971d-5d1d-9baa-308703647df5
-- title:
--   Real Covolume: is Add Haar vol
-- statement:
--   The Real Covolume construction uses the is Add Haar vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean#L58-L61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem Formalism.L2.SG.Pf.RealCovolume.isAddHaar_vol : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := by sorry
