-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_cfg_interlaces
-- name    : Formalism.FourierDecayAlt.P.CutMP.cfg_interlaces
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:21:15.947798+00:00
-- url     : https://prove2.me/theorems/6c990f51-73a8-4d2b-9db9-fb46b3fd2d5a
-- title:
--   Cut MP: cfg interlaces
-- statement:
--   The Cut MP construction uses the cfg interlaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLam.lean#L50-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutLam.lean#L50-L123

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
variable (c : Sz.Cfg)

theorem Formalism.FourierDecayAlt.P.CutMP.cfg_interlaces (r : ℕ) (hm : c.m = 2 * r + 2) (hk : 2 ≤ c.k) (hok : c.Ok) (de : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) :
    C7.LamInterlaces c.k r (c.u de) (fun s : Fin (c.k + 2 * r + 1) => c.lam ((s : ℕ) + 1)) := by sorry
