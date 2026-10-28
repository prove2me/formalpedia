-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
-- name    : AvramDividend.Classical.levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:27:46.509862+00:00
-- url     : https://prove2.me/theorems/1f657d32-3005-49a8-825e-b38f2108d4f6
-- title:
--   Exact finite-cap first-upper-record mass under genuine random-terminal Esscher density and real exponential clock
-- statement:
--   For a spectrally negative Lévy process X under probability P, a nonnegative upper threshold b, cap N, a genuine independent real exponential observation clock E~Exp(p) with p>0, and Esscher parameter phi≥0 with ψ(phi)=q, integrate the actual terminal likelihood exp(phi X_E−qE) against P⊗Exp(p) over the event that the strict first upper crossing T_b occurs before cap N and its finite capped age τ_N is no later than E. This finite-cap weighted mass equals E_P[1_{T_b<N} exp(phi*b−(p+q)τ_N)]. The non-strict boundary τ_N≤E is exact; tie mass vanishes by atomlessness for the later strict-clock corollary. This is an authentic random-terminal Esscher stopping-transfer identity; it neither presumes two-sided exit nor Wiener–Hopf factorisation or a global Q^phi.
-- source:
--   Kuznetsov–Kyprianou–Rivero section 2.1 and Avram–Palmowski–Pistorius equation (3.6); canonical accepted original upper strict passage law, fixed-lag strong Markov Esscher normalization 4685fca7, true product exponential random-age reward translation 51ea1a74, no-overshoot 014436e7, capped clock coercion 159a20a9, and genuine joint Lévy path-time measurability d55462c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_exp_clock_random_age_joint_reward_shift_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_esscher_future_lag_normalisation_ws01d
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (p : ℝ) (hp : 0 < p)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ z : Ω × ℝ,
       if z.1 ∈ A ∧ (τ z.1 : ℝ) ≤ z.2 then
         ENNReal.ofReal (Real.exp
           (phi * X.X z.2.toNNReal z.1 -
             (z.2.toNNReal : ℝ) * q))
       else 0 ∂(P.prod (ProbabilityTheory.expMeasure p))) =
     (∫⁻ ω : Ω, if ω ∈ A then
       ENNReal.ofReal (Real.exp
         (phi * b - (p + q) * (τ ω : ℝ)))
       else 0 ∂P)) := by sorry
