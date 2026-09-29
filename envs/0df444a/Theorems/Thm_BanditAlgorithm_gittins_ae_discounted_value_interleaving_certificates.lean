-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_ae_discounted_value_interleaving_certificates
-- name    : BanditAlgorithm.gittins_ae_discounted_value_interleaving_certificates
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T16:29:16.251268+00:00
-- url     : https://prove2.me/theorems/7d573013-821e-463a-a664-d7ddcb56989d
-- title:
--   Almost-sure prevailing-charge interleaving certificates
-- statement:
--   Consider a discounted rested Markov bandit with finitely many arms, common transition kernel $P$, measurable reward $r$, discount factor $0<\alpha<1$, and initial state vector $x$. Assume discounted absolute rewards are integrable and that every single-arm Gittins index admits arbitrarily accurate stopping-time calibration. Let $\pi^\star$ always select an arm of maximal current Gittins index, and let $\pi$ be any competing policy.
--
--   There is a common probability-space measure carrying the policy-independent Markov state stacks and action interleavings of both policies such that, for every $\varepsilon>0$, one can construct random finite lists $X$ and $Y$ satisfying almost surely
--
--   $$
--   X\sim_{\mathrm{perm}}Y,\qquad Y_1\ge Y_2\ge\cdots,
--   $$
--
--   and whose discounted folds obey
--
--   $$
--   V_\alpha(\pi,x)\le \mathbb E[\operatorname{Fold}_\alpha(X)]+\varepsilon,\qquad
--   \mathbb E[\operatorname{Fold}_\alpha(Y)]\le V_\alpha(\pi^\star,x)+\varepsilon.
--   $$
--
--   These are the finite almost-sure certificates in the prevailing-charge proof: $X$ is the competing interleaving of decreasing arm stacks, while $Y$ is the greedy nonincreasing interleaving on the same sample point. The statement isolates the model-specific reward-stack coupling needed by the reusable probabilistic Hardy--Littlewood limit theorem.
--
--   **Formalization Note** The common sample type stores the arm trajectories and two action sequences. The theorem existentially supplies its coupling measure. The folds are integrable real random variables, list permutation is pointwise almost surely, and `Pairwise (· ≥ ·)` expresses nonincreasing order.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 35.9, Part 1 and Part 2, printed pp. 451–453 / PDF pp. 460–462; finite interleaving inequality Lemma 35.10 on printed p. 451.

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_ae_discounted_value_interleaving_certificates
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (hcal : ∀ (y : S) (ε : ℝ), 0 < ε →
      ∃ τ : (ℕ → S) → ℕ∞,
        IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        gittinsIndex P r α y - ε <
          (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
            (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
              ∂markovChainMeasure P y))
    (πstar : MarkovBanditPolicy k S)
    (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (π : MarkovBanditPolicy k S) :
    ∃ μ : Measure
        ((Fin k → ℕ → S) × ((ℕ → Fin k) × (ℕ → Fin k))),
      ∀ ε : ℝ, 0 < ε →
        ∃ xs ys :
            ((Fin k → ℕ → S) × ((ℕ → Fin k) × (ℕ → Fin k))) →
              List ℝ,
          (∀ᵐ ω ∂μ, (xs ω).Perm (ys ω) ∧
            (ys ω).Pairwise (· ≥ ·)) ∧
          Integrable
            (fun ω ↦ (xs ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
          Integrable
            (fun ω ↦ (ys ω).foldr (fun z acc ↦ z + α * acc) 0) μ ∧
          markovBanditDiscountedValue P r α π x ≤
            (∫ ω, (xs ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) + ε ∧
          (∫ ω, (ys ω).foldr (fun z acc ↦ z + α * acc) 0 ∂μ) ≤
            markovBanditDiscountedValue P r α πstar x + ε := by
  sorry
