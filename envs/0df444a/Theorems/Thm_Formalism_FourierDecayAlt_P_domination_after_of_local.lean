-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_domination_after_of_local
-- name    : Formalism.FourierDecayAlt.P.domination_after_of_local
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:39.091796+00:00
-- url     : https://prove2.me/theorems/20c4b595-f9e9-4baa-9ae8-28cdeca71f12
-- title:
--   P: domination after of local
-- statement:
--   The P construction uses the domination after of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L256-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L256-L256

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

theorem Formalism.FourierDecayAlt.P.domination_after_of_local : Formalism.FourierDecayAlt.TC.DomAfterOfLocal := by sorry
