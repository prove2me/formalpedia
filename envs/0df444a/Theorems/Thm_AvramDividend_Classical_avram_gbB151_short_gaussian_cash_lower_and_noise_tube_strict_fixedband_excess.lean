-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
-- name    : AvramDividend.Classical.avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:11:23.632645+00:00
-- url     : https://prove2.me/theorems/38d1b92f-6af5-4acf-8beb-31b141986d00
-- title:
--   Quantitative short positive-Gaussian cash lower plus bounded noise forces strict failure of fixed-band cash bound
-- statement:
--   For T=1/1000, earlier physical time S=99/100000, cap C=1/8, quadratic payoff w(y)=2y-4y², terminal reserve y≥249/2000, cumulative dividends d≥173/100000, and centred source noise |N|≤1/4000, any genuine discounted cash lower bound F≥e^(-qS)d+e^(-qT)w(y) contradicts F-w(C)≤N+1/1936. This proves a strictly positive rational margin without assuming any exact Ito cash identity; only the actual Stieltjes cash lower bound and original L1 noise estimate remain to be supplied.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
    (y d F N : ℝ)
    (hylo : (249 / 2000 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ))
    (hdlo : (173 / 100000 : ℝ) ≤ d)
    (hN : |N| ≤ (1 / 4000 : ℝ))
    (hCash : Real.exp (-(99 / 10000000 : ℝ)) * d +
        Real.exp (-(1 / 100000 : ℝ)) * (2 * y - 4 * y ^ 2) ≤ F) :
    ¬ F - (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by sorry
