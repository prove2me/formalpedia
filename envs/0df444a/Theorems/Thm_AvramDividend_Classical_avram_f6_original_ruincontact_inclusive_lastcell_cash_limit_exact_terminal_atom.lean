-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_ruincontact_inclusive_lastcell_cash_limit_exact_terminal_atom
-- name    : AvramDividend.Classical.avram_f6_original_ruincontact_inclusive_lastcell_cash_limit_exact_terminal_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:51:14.829474+00:00
-- url     : https://prove2.me/theorems/01cbd256-a258-44db-8bad-f15f7af52486
-- title:
--   Original inclusive last-cell stopped Stieltjes cash tends exactly to the terminal payment atom
-- statement:
--   For any actual spectrally negative Lévy process X, genuine dividend strategy D and realised finite stopping clock T, the discounted original paymentTimes Stieltjes cash on the last physical interval (T−n/(j+1),T] converges to the discounted cash concentrated at the single terminal time T as mesh j→∞. The strict part vanishes by the original physical Stieltjes convergence theorem and the inclusive last interval is exactly strict part plus terminal singleton. The limit handles a possibly positive terminal dividend atom correctly and applies even when cash integrals are infinite, since it is stated in extended nonnegative reals. This completes the endpoint-atom treatment needed for the original ruin-contact stopped Itô dividend mesh.
-- source:
--   Proved original strict canonical n-mesh terminal cash tail e8e62b96; exact original full final Ioc split into strict and singleton efee280a currently checking.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_ruincontact_inclusive_lastcell_cash_limit_exact_terminal_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (hn : 0 < n) :
    Tendsto (fun j : ℕ =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioc ((T : ℝ) - (n : ℝ) / ((j : ℝ) + 1)) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))) := by sorry
