-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_blk_apply
-- name    : Formalism.L2.Pj.DatLin.blk_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:55.431725+00:00
-- url     : https://prove2.me/theorems/3368c0c5-ee6c-4f7a-8147-e84e01a36e99
-- title:
--   Dat Lin: blk apply
-- statement:
--   The Dat Lin construction uses the blk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L120-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L120-L120

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

theorem Formalism.L2.Pj.DatLin.blk_apply (N : ι → Matrix n n ℂ) (u : ι → n → ℂ) (τ : ι) : blk N u τ = N τ *ᵥ u τ := by sorry
