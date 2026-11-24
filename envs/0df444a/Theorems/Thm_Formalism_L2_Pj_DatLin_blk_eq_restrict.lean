-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_blk_eq_restrict
-- name    : Formalism.L2.Pj.DatLin.blk_eq_restrict
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:21.983849+00:00
-- url     : https://prove2.me/theorems/b6106069-bd8f-44a4-8204-b8f26037345e
-- title:
--   Dat Lin: blk eq restrict
-- statement:
--   The Dat Lin construction uses the blk eq restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L133-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L133-L133

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]

theorem Formalism.L2.Pj.DatLin.blk_eq_restrict (N : ι → Matrix n n ℂ) : blk N = (blkC N).restrictScalars ℝ := by sorry
