-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_ae_pi_all
-- name    : Formalism.FourierDecayAlt.P.OrderChainWeights.ae_pi_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:03.465842+00:00
-- url     : https://prove2.me/theorems/14b13975-fd13-4b77-9469-bc738ad4f4dc
-- title:
--   Order Chain Weights: ae pi all
-- statement:
--   The Order Chain Weights construction uses the ae pi all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderChainWeights.lean#L41-L46

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderChainWeights
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal

theorem Formalism.FourierDecayAlt.P.OrderChainWeights.ae_pi_all {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (i : ℕ)
    (p : X → Prop) (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ h ∂(Measure.pi fun _ : Fin i => μ), ∀ l, p (h l) := by sorry
