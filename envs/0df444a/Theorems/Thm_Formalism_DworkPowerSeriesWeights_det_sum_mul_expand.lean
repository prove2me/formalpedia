-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_det_sum_mul_expand
-- name    : Formalism.DworkPowerSeriesWeights.det_sum_mul_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:58.182398+00:00
-- url     : https://prove2.me/theorems/5d472671-d6a9-43b2-b9a1-603d70f23a64
-- title:
--   Dwork Power Series Weights: det sum mul expand
-- statement:
--   The Dwork Power Series Weights construction uses the det sum mul expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean#L10-L19

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.det_sum_mul_expand {S : Type*} [CommRing S] {p n : ℕ} (u : Fin p → Fin n → S)
    (y : Fin n → Fin p → S) :
    (Matrix.of fun (r r' : Fin p) => ∑ a, u r a * y a r').det =
      ∑ A : Fin p → Fin n, (∏ r', y (A r') r') *
        (Matrix.of fun (r r' : Fin p) => u r (A r')).det := by sorry
