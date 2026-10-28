-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_independent_exponential_clock_product_probability
-- name    : AvramDividend.Classical.chat04_independent_exponential_clock_product_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:25:20.130022+00:00
-- url     : https://prove2.me/theorems/f74d294c-54ce-498c-8236-12f0c2c4280f
-- title:
--   Construct an independent exponential observation clock on a genuine joint probability space
-- statement:
--   For any genuine probability law P on a measurable sample space Ω and any exponential clock rate p>0, there exists a genuine probability measure R on Ω×ℝ whose path marginal is exactly P and whose time marginal is the exponential probability law Exp(p). The construction takes the product probability P⊗Exp(p), giving the correct independent exponential observation clock required in the finite-rate Wiener–Hopf factorisation. Unlike a formal P^φ path law at infinity, this genuinely exists for any fixed original or finite-horizon Esscher probability P.
-- source:
--   Pinned Mathlib already constructs `ProbabilityTheory.expMeasure p` and proves it is a probability for p>0. Its product with the supplied probability P is a probability by `Measure.prod.instIsProbabilityMeasure`, and `Measure.fst_prod` / `Measure.snd_prod` establish the two exact marginals. This is the first concrete step to form the independent exponential stopping horizon without assuming a nonexistent global Esscher-tilted Lévy process.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory ProbabilityTheory

theorem AvramDividend.Classical.chat04_independent_exponential_clock_product_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p) :
    ∃ R : Measure (Ω × ℝ),
      IsProbabilityMeasure R ∧
      R.fst = P ∧
      R.snd = ProbabilityTheory.expMeasure p := by sorry
