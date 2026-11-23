-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_domAfterOfLocal
-- name    : Formalism.FourierDecayAlt.P.DensitySumsAndDomination.domAfterOfLocal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:05.536799+00:00
-- url     : https://prove2.me/theorems/b4620dbb-411a-4011-b628-55960afb959d
-- title:
--   Density Sums And Domination: dom After Of Local
-- statement:
--   The Density Sums And Domination construction uses the dom After Of Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L112-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L112-L142

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination

theorem Formalism.FourierDecayAlt.P.DensitySumsAndDomination.domAfterOfLocal : DomAfterOfLocal := by sorry
