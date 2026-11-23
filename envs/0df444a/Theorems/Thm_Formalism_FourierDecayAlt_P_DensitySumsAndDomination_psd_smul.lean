-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_psd_smul
-- name    : Formalism.FourierDecayAlt.P.DensitySumsAndDomination.psd_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:30:00.709822+00:00
-- url     : https://prove2.me/theorems/2e8a74fe-a4f4-4614-a432-0e2d5d69a7be
-- title:
--   Density Sums And Domination: psd smul
-- statement:
--   The Density Sums And Domination construction uses the psd smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L18-L31

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

theorem Formalism.FourierDecayAlt.P.DensitySumsAndDomination.psd_smul {α : Type} {Y : Finset α} {k : α → α → ℂ} (c : ℝ) (hc : 0 ≤ c) (h : TB.PSDOn Y k) :
    TB.PSDOn Y (fun x y => (c : ℂ) * k x y) := by sorry
