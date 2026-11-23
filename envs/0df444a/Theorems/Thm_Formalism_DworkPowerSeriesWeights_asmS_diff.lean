-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmS_diff
-- name    : Formalism.DworkPowerSeriesWeights.asmS_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:54:10.268807+00:00
-- url     : https://prove2.me/theorems/672f97f4-0569-40df-8337-0ef3d54355aa
-- title:
--   Dwork Power Series Weights: asm S diff
-- statement:
--   The Dwork Power Series Weights construction uses the asm S diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L98-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffEvenDerivativeEqZero.lean#L98-L163

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries

theorem Formalism.DworkPowerSeriesWeights.asmS_diff (hGW : GenLogWeight.{u, 0}) (hGI : GenLogInverse.{u, 0}) (hB : LogBridges.{u})
    (hSW : SubstWt.{u, 0, 0}) (hQ : Quant.{u}) (hLS : LogStep.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l d : ℕ} [NeZero d]
    (hl : l.Prime) (hd : 2 ≤ d) (hde : Even d) (hpi : ‖(l : K)‖ < 1)
    {K0 : Subfield K} (hK0 : Unram l K0) (D : MvPowerSeries (V2 d) K)
    (hD0 : constantCoeff D = 0) (hK : ∀ n, coeff n (mvExp D) ∈ K0)
    (hcong : ∀ n : V2 d →₀ ℕ, coeff n (mvExp D) ≠ 0 →
      ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l x.2)
    (hEi : Integral (subst (letterLog (K := K) l) (mvExp D)))
    (hEc : constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1) :
    WtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) D := by sorry
