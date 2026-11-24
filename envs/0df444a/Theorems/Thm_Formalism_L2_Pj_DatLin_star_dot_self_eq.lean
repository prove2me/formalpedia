-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_star_dot_self_eq
-- name    : Formalism.L2.Pj.DatLin.star_dot_self_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:42.333324+00:00
-- url     : https://prove2.me/theorems/89d7b5ae-a2c7-48c1-bcd0-54862348fe1d
-- title:
--   Dat Lin: star dot self eq
-- statement:
--   The Dat Lin construction uses the star dot self eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L17-L18

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

theorem Formalism.L2.Pj.DatLin.star_dot_self_eq (w : m → ℂ) : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by sorry
