-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx1_star_sc
-- name    : Formalism.FourierDecayAlt.P.Mx1.star_sc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:29.321802+00:00
-- url     : https://prove2.me/theorems/459731d9-f653-4736-bb7d-97e74254f7d5
-- title:
--   Mx1: star sc
-- statement:
--   The Mx1 construction uses the star sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MultiplicationOpHom.lean#L21-L28

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx1

theorem Formalism.FourierDecayAlt.P.Mx1.star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by sorry
