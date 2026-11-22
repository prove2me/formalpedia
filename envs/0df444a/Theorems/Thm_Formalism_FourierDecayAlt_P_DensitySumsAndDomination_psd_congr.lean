-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_psd_congr
-- name    : Formalism.FourierDecayAlt.P.DensitySumsAndDomination.psd_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:30.317864+00:00
-- url     : https://prove2.me/theorems/af0d84fb-8834-4ed4-adf2-e2bccd553ffc
-- title:
--   Density Sums And Domination: psd congr
-- statement:
--   The Density Sums And Domination construction uses the psd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L9-L16

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

theorem Formalism.FourierDecayAlt.P.DensitySumsAndDomination.psd_congr {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y) (hk : TB.PSDOn Y k) : TB.PSDOn Y k' := by sorry
