-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_domScaleTop
-- name    : Formalism.FourierDecayAlt.P.DensitySumsAndDomination.domScaleTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:14.468887+00:00
-- url     : https://prove2.me/theorems/b23357c7-67fb-4ede-a514-2d7809995fe2
-- title:
--   Density Sums And Domination: dom Scale Top
-- statement:
--   The Density Sums And Domination construction uses the dom Scale Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L33-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L33-L64

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

theorem Formalism.FourierDecayAlt.P.DensitySumsAndDomination.domScaleTop : DomScaleTop := by sorry
