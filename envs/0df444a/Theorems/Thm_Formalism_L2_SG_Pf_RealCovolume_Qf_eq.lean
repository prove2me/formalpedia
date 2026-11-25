-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_Qf_eq
-- name    : Formalism.L2.SG.Pf.RealCovolume.Qf_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:12.693622+00:00
-- url     : https://prove2.me/theorems/17bbcc04-0081-4dbd-b1b1-7413aedf4793
-- title:
--   Real Covolume: Qf eq
-- statement:
--   The Real Covolume construction uses the Qf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean#L35-L39

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

theorem Formalism.L2.SG.Pf.RealCovolume.Qf_eq (g : κ → ℝ) (a b : ι → κ → ℂ) :
    Qf g a b = ∑ p : ι × κ × Fin 2, reCo a p * reCo b p * g p.2.1 := by sorry
