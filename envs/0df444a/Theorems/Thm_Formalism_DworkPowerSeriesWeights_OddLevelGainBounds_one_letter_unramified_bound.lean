-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_one_letter_unramified_bound
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.one_letter_unramified_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:23.926932+00:00
-- url     : https://prove2.me/theorems/93ac58af-a7bb-4261-a864-6140df5fa5b7
-- title:
--   Odd Level Gain Bounds: one letter unramified bound
-- statement:
--   The Odd Level Gain Bounds construction uses the one letter unramified bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L15-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L15-L55

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.one_letter_unramified_bound (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (l N0 N1 : ℕ) (hl : l.Prime) (hodd : Odd l) (hpi : ‖(l : K)‖ < 1)
    (K0 : Subfield K) (hK0 : Unram l K0) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
    (be : MvPowerSeries (ZMod 2) K) (hbe : BHyp l 2 K0 ζ be) (ep : K) (hep : ‖ep‖ = 1)
    (ι : Type v) [Fintype ι] (M : Fin N0 × Fin N1 → ι → K) (hM1 : ∀ x i, ‖M x i‖ ≤ 1)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (hg0 : ∀ x, MvPowerSeries.constantCoeff (g x) = 0)
    (hg : ∀ x, MvPowerSeries.subst g (oneLog (K := K) l x) = MvPowerSeries.X x)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (hU : Integral U)
    (sgn : K) (hsgn : sgn = 1 ∨ sgn = -1) (κ : ι →₀ ℕ) (a : ℕ) (ha : 1 ≤ a)
    (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
            (MvPowerSeries.subst g U) *
          mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
              ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be))‖ ≤
      ‖(l : K)‖ ^ (rho l * (κ.degree : ℝ) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by sorry
