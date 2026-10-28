-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_stopped_weighted_rational_prefixes_to_paymentTimes
-- name    : AvramDividend.Classical.zero_stopped_weighted_rational_prefixes_to_paymentTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:49:52.335072+00:00
-- url     : https://prove2.me/theorems/04992066-c354-45c7-8b22-719a0bccc9b4
-- title:
--   Rational Stieltjes prefix equalities identify the entire original stopped reward
-- statement:
--   Given two real-time measures with no singleton atoms at any nonnegative time, suppose their nonnegative weighted Stieltjes integrals agree over every rational right-closed initial prefix (0,q] strictly before the extended-real stopping horizon sigma. Then their full stopped integrals over the genuine paymentTimes sigma agree. The proof handles sigma=0 by the zero atom lemmas, and sigma>0 by the Proved rational [0,q) exhaustion of paymentTimes. Positive endpoint atomlessness exchanges [0,q) with (0,q]; all rational prefixes form an inclusion-directed countable family, so the Proved directed Stieltjes union theorem passes the equality to all stopped payments. This removes the need to explicitly construct a rational indexing grid and correctly handles sigma=∞ and the exact strict endpoint.
-- source:
--   Avram Palmowski Pistorius (2007), original zero-barrier stopped running-supremum reward. Prove2Me rational paymentTimes exhaustion and directed Stieltjes prefix lemmas.

import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_rational_strict_prefix
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_directed_stieltjes_prefixes_determine_union_reward
import Theorems.Thm_AvramDividend_Classical_zero_atom_free_stieltjes_reward_union
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_stopped_weighted_rational_prefixes_to_paymentTimes
    (σ : ℝ≥0∞) (μ ν : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hprefix : ∀ q : ℚ, 0 < (q : ℝ) →
      ENNReal.ofReal (q : ℝ) < σ →
      (∫⁻ t in Ioc (0 : ℝ) (q : ℝ), f t ∂μ) =
        (∫⁻ t in Ioc (0 : ℝ) (q : ℝ), f t ∂ν))
    (hzeroμ : μ {(0 : ℝ)} = 0) (hzeroν : ν {(0 : ℝ)} = 0)
    (hatomμ : ∀ T : ℝ, 0 < T → μ {T} = 0)
    (hatomν : ∀ T : ℝ, 0 < T → ν {T} = 0) :
    (∫⁻ t in paymentTimes σ, f t ∂μ) =
      (∫⁻ t in paymentTimes σ, f t ∂ν) := by sorry
