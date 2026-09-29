-- Prove2me | Theorems.Thm_BanditAlgorithm_posterior_diagonal_representation
-- name    : BanditAlgorithm.posterior_diagonal_representation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T04:29:15.65254+00:00
-- url     : https://prove2.me/theorems/b4f87df1-3c35-4a30-a1e3-2f78cdfa8467
-- title:
--   Posterior diagonal representation for Thompson sampling
-- statement:
--   Let $R$ be a posterior law on a latent state $X$, let $A^*=\operatorname{opt}(X)$ take values in $\{0,\ldots,k-1\}$, and independently sample an action $A$ with the posterior law of $A^*$. For each action $a$, let $Y_a\in[0,1]$ be its reward. Then there are posterior arm probabilities $p_a$ and probability laws $P_a,M_a$ on $[0,1]$ such that every $D(P_a\|M_a)$ is finite,
--
--   $$
--   \mathbb E[Y_{A^*}-Y_A]=\sum_a p_a\bigl(\mathbb E_{P_a}Y-\mathbb E_{M_a}Y\bigr),
--   $$
--
--   and the diagonal information terms satisfy
--
--   $$
--   \sum_a p_a^2D(P_a\|M_a)\le I\bigl(A^*;(A,Y_A)\bigr).
--   $$
--
--   This is the reusable posterior-measure core of the Thompson-sampling information-ratio argument. It explicitly handles zero-posterior-probability arms by taking $P_a=M_a$.
--
--   **Formalization Note** Rewards are represented as values of the subtype $[0,1]$, and mutual information is represented by KL divergence between the joint law and the product of its marginals.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (2020), Lemma 36.7 and equation (36.9), printed p. 470 / free PDF p. 479.

import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_ne_top
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

theorem posterior_diagonal_representation
    {k : ℕ} [NeZero k]
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (R : Measure X) [IsProbabilityMeasure R]
    (opt : X → Fin k) (hopt : Measurable opt)
    (reward : Fin k → X → Set.Icc (0 : ℝ) 1)
    (hreward : ∀ a, Measurable (reward a)) :
    let q := Measure.map opt R
    let rho := R.prod q
    let obs := fun z : X × Fin k ↦ (z.2, reward z.2 z.1)
    ∃ (p : Fin k → ℝ)
      (P M : Fin k → Measure (Set.Icc (0 : ℝ) 1)),
      (∀ a, IsProbabilityMeasure (P a)) ∧
      (∀ a, IsProbabilityMeasure (M a)) ∧
      (∀ a, klDiv (P a) (M a) ≠ ∞) ∧
      (∫ z, ((reward (opt z.1) z.1).1 - (reward z.2 z.1).1) ∂rho) =
        ∑ a, p a * ((∫ z, z.1 ∂P a) - ∫ z, z.1 ∂M a) ∧
      (∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal) ≤
        (klDiv (Measure.map (fun z ↦ (opt z.1, obs z)) rho)
          (q.prod (Measure.map obs rho))).toReal := by sorry
