-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx9_eq_ofReal
-- name    : Formalism.FourierDecayAlt.P.Mx9.eq_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:41.453683+00:00
-- url     : https://prove2.me/theorems/90fbc7ea-1b82-495b-af93-d1542a007b04
-- title:
--   Mx9: eq of Real
-- statement:
--   The Mx9 construction uses the eq of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L9-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModelWordsAssemble.lean#L9-L9

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

theorem Formalism.FourierDecayAlt.P.Mx9.eq_ofReal {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := by sorry
