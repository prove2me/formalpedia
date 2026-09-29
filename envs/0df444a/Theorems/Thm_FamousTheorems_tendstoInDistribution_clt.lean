-- Prove2me | Theorems.Thm_FamousTheorems_tendstoInDistribution_clt
-- name    : FamousTheorems.tendstoInDistribution_clt
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:06:19.312193+00:00
-- url     : https://prove2.me/theorems/b72f4798-7e27-424e-9e5a-dae6b6de865b
-- title:
--   The central limit theorem
-- statement:
--   **The central limit theorem.**
--
--   Let $X_0, X_1, \dots$ be independent, identically distributed real random variables with finite
--   second moment, mean $\mu = \mathbb{E}[X_0]$ and variance $v = \operatorname{Var}(X_0)$. Then
--   $$\frac{1}{\sqrt{n}}\left(\sum_{k<n} X_k - n\mu\right) \;\xrightarrow{\;d\;}\; \mathcal{N}(0, v).$$
--
--   The remarkable content is universality: the limit does not remember the distribution of $X_0$ at all,
--   only its mean and variance. A sum of many small independent contributions is Gaussian whether the
--   summands are coin flips, dice, or anything else with finite variance. This is why the normal
--   distribution appears everywhere in statistics and physics, and it is the reason a $\sqrt{n}$ scaling
--   is the right one — any other power gives either $0$ or divergence.
--
--   De Moivre proved the case of fair coin flips in 1733; Laplace extended it to general binomial
--   trials. The modern general statement with necessary and sufficient conditions is due to Lindeberg
--   (1920), Lévy and Feller. Along with the law of large numbers it is one of the two pillars of
--   classical probability: the law of large numbers says the average converges, and the central limit
--   theorem describes the size and shape of the error.
--
--   **Formalization note.** `TendstoInDistribution` is weak convergence of the laws; `HasLaw Y (gaussianReal 0 v) P'`
--   says $Y$ is a centred Gaussian of variance $v$ under $P'$, and `MemLp (X 0) 2 P` is the finite-second-moment
--   hypothesis. The result is Mathlib's `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem tendstoInDistribution_clt {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 (Var[X 0; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' := by sorry

end FamousTheorems
