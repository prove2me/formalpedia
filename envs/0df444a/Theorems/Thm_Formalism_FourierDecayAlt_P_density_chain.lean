-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_density_chain
-- name    : Formalism.FourierDecayAlt.P.density_chain
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:42.299279+00:00
-- url     : https://prove2.me/theorems/dc877003-7866-413d-b616-88fe9e5e7cae
-- title:
--   P: density chain
-- statement:
--   The P construction uses the density chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L260-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L260-L260

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.density_chain : Formalism.FourierDecayAlt.TC.DensChain := by sorry
