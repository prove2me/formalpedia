-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_star_mulVec_dot
-- name    : Formalism.L2.Pj.DatLin.star_mulVec_dot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:19.491297+00:00
-- url     : https://prove2.me/theorems/767d5239-5463-4525-baf2-7cac5bdd3ea4
-- title:
--   Dat Lin: star mul Vec dot
-- statement:
--   The Dat Lin construction uses the star mul Vec dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L13-L15

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
variable {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.L2.Pj.DatLin.star_mulVec_dot (A B : Matrix m m ℂ) (u w : m → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ w) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ w) := by sorry
