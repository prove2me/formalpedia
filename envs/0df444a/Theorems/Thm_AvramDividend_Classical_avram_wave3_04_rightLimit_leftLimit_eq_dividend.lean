-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
-- name    : AvramDividend.Classical.avram_wave3_04_rightLimit_leftLimit_eq_dividend
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:28:55.100432+00:00
-- url     : https://prove2.me/theorems/f9c3a5c4-3a58-45b7-b6da-8734693b863d
-- title:
--   The strict-left limit of post-payment dividends is the original cumulative payment
-- statement:
--   Let D be any adapted, nondecreasing, left-continuous cumulative dividend strategy, and define D⁺(s) as the right-hand limit after the payment at time s. At each strictly positive time t, the limit of D⁺(s) as s approaches t from below is D(t):
--
--   $$\lim_{s\uparrow t}D_{s+}=D_t.$$
--
--   This identifies the exact pre-jump dividend amount of the càdlàg right-limit modification. It applies to diffuse, singular-continuous and right-atomic payment paths, so that a controlled Lévy process can use its pre-jump reserve in stochastic integration while retaining the original Stieltjes dividend convention.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), verification of admissible nondecreasing left-continuous dividends: https://avram.perso.univ-pau.fr/papers/Martijn/dividend.pdf. Mathematical step: original cumulative payment is the left limit of its right-continuous modification; follows from monotonicity, left continuity and order-topological squeeze. Original pinned remote elaboration succeeded to sentinel in private probe d5e59d4b-7725-45cc-afdf-8b3d9b9bd993.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_rightLimit_leftLimit_eq_dividend
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun s : ℝ≥0 => rightLimit D s ω)
      (𝓝[<] t) (𝓝 (D t ω)) := by sorry
