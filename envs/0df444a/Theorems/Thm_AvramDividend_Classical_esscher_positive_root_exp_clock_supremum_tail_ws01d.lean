-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_tail_ws01d
-- name    : AvramDividend.Classical.esscher_positive_root_exp_clock_supremum_tail_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:34:50.844043+00:00
-- url     : https://prove2.me/theorems/0e6d186f-abc0-4a83-9008-29e1b432641a
-- title:
--   Exact genuine random-terminal Esscher supremum upper tail at an independent exponential observation time
-- statement:
--   For spectrally negative Lévy X under P, b>0, phi>0 with ψ(phi)=q>0, independent real E~Exp(p), p>0 and lam>0 with ψ(phi+lam)-q=p, under the genuine random-terminal probability law defined by weighting P⊗Exp(p) by exp(phi X_E-q E), the actual running supremum over 0≤s≤E has strict tail Ptilt(S_E>b)=exp(-lam*b). The real clock is clamped toNNReal inside the density and path functional; the non-strict finite-passage/clock mass transfer is corrected to strict running supremum by a proved null tie set. No global Q^phi, deterministic Q_T transfer, WH independence or two-sided exit formula is assumed.
-- source:
--   Kuznetsov–Kyprianou–Rivero Section 2.1 equations 2.2–2.7 and Section 2.5, Avram–Palmowski–Pistorius (2007) equation 3.6; canonically Proved true terminal uncapped Esscher first-passage bridge e5ca1e66-c551-4ac5-a85c-b0a5abd8ed9e, accepted candidate 17587, exact passage discount 0da3763f, strict running-sup/first-passage b626324c, true clock extrema measurability 4390c2cb and pinned Mathlib withDensity_apply/lintegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_exp_clock_supremum_tail_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (phi q : ℝ) (hphi : 0 < phi) (hq : 0 < q) (hroot : X.ψ phi = q)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (phi + lam) - q = p)
    (b : ℝ) (hb : 0 < b) :
    ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q))))
      {z : Ω × ℝ | b < runningSup X z.2.toNNReal z.1} =
      ENNReal.ofReal (Real.exp (-(lam * b))) := by sorry
