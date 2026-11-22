-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_xC_ne
-- name    : Formalism.FourierDecayAlt.P.Mx9.xC_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:13.192564+00:00
-- url     : https://prove2.me/theorems/36b483c4-d423-43f7-9806-9c74e2a54865
-- title:
--   Mx9: x C ne
-- statement:
--   The Mx9 construction uses the x C ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L25-L31

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelWordsAssemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M
open Formalism.FourierDecayAlt.P.Mx9

theorem Formalism.FourierDecayAlt.P.Mx9.xC_ne (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by sorry
