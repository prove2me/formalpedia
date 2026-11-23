-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_Icc_one_eq
-- name    : Formalism.FourierDecayAlt.P.Sz6.Icc_one_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:18.423004+00:00
-- url     : https://prove2.me/theorems/b0916677-8c62-4822-8110-cad56717022e
-- title:
--   Sz6: Icc one eq
-- statement:
--   The Sz6 construction uses the Icc one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L18-L19

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6

theorem Formalism.FourierDecayAlt.P.Sz6.Icc_one_eq (n : ℕ) : Icc 1 n = Ico 1 (n + 1) := by sorry
