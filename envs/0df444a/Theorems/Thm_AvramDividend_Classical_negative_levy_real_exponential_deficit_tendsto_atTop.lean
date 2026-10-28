-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_real_exponential_deficit_tendsto_atTop
-- name    : AvramDividend.Classical.negative_levy_real_exponential_deficit_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:20:31.435359+00:00
-- url     : https://prove2.me/theorems/d8e8101f-e098-4037-b2a8-032d4ed07701
-- title:
--   Infinite negative Lévy activity forces divergence of integrable real exponential jump deficits
-- statement:
--   A measure supported on strictly negative jumps with infinite mass has real exponential deficit integral ∫(1−exp(ny))dν diverging to +∞ as n→∞, provided each integral is finite and integrable. This converts the already proved ENNReal monotone-convergence theorem to ordinary real integration via the pinned-Mathlib ofReal integral identity and the topological equivalence between ofReal convergence to infinity and real convergence to atTop.
-- source:
--   Monotone convergence and Lévy–Khintchine exponent asymptotics, Kuznetsov Kyprianou Rivero Theory of Scale Functions, and Avram Palmowski Pistorius (2007), https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_negative_levy_exponential_deficit_tendsto_top
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- Integrable real negative-jump deficits diverge when negative activity is infinite. -/
theorem negative_levy_real_exponential_deficit_tendsto_atTop
    (ν : Measure ℝ)
    (hsupport : ν (Ici (0 : ℝ)) = 0)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (hInt : ∀ n : ℕ, Integrable
      (fun y : ℝ => 1 - Real.exp ((n : ℝ) * y)) ν) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ, (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop atTop := by sorry

end AvramDividend.Classical
