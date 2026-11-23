-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_norm_coeff_rename_le
-- name    : Formalism.DworkPowerSeriesWeights.OrbMul.norm_coeff_rename_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:26.486802+00:00
-- url     : https://prove2.me/theorems/ebb9b8d9-afaf-4e37-8e3d-c130a22b33ea
-- title:
--   Orb Mul: norm coeff rename le
-- statement:
--   The Orb Mul construction uses the norm coeff rename le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L71-L79

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
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
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OrbMul
variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ₁ σ₂ : Type}

theorem Formalism.DworkPowerSeriesWeights.OrbMul.norm_coeff_rename_le {σ τ : Type} (e : σ → τ) (he : Function.Injective e)
    (A : MvPolynomial σ K) {B : ℝ} (hA : ∀ n, ‖MvPolynomial.coeff n A‖ ≤ B) (n : τ →₀ ℕ) :
    ‖MvPolynomial.coeff n (MvPolynomial.rename e A)‖ ≤ B := by sorry
