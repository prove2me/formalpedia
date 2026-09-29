-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_ae_certificates_of_greedy_charge_interleaving
-- name    : BanditAlgorithm.gittins_ae_certificates_of_greedy_charge_interleaving
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T21:12:35.915155+00:00
-- url     : https://prove2.me/theorems/d59103f0-1b6e-4cbd-8e1c-f06ea4603088
-- title:
--   Gittins certificate bridge from greedy charge interleavings
-- statement:
--   Consider a discounted finite-armed Markov bandit with transition kernel $P$, measurable reward $r$, discount factor $0<\alpha<1$, and an integrability assumption ensuring that discounted rewards are well defined. Assume the stated stopping-time calibration of the Gittins index, and let $\pi^*$ be a Gittins-index policy.
--
--   Assume also the deterministic charge-stack principle: for every family of nonincreasing stacks, every greedy interleaving has discounted sum at least that of any competing interleaving. Then for every competing policy $\pi$ there is a common probability measure $\mu$ such that, for every $\varepsilon>0$, measurable finite lists $x_\omega$ and $y_\omega$ satisfy almost surely that $y_\omega$ is a nonincreasing permutation of $x_\omega$, both discounted list values are integrable, and
--
--   $$
--   V_\alpha(\pi,x)
--   \le \int D_\alpha(x_\omega)\,d\mu+\varepsilon,
--   \qquad
--   \int D_\alpha(y_\omega)\,d\mu
--   \le V_\alpha(\pi^*,x)+\varepsilon.
--   $$
--
--   This theorem isolates the probabilistic reward-stack coupling, prevailing-charge comparison, and infinite-horizon tail passage from the deterministic Hardy--Littlewood interleaving inequality.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, Section 35.4, printed pp. 451--453 / PDF pp. 459--461: Lemma 35.10 and the proof of Theorem 35.9, especially Part 1 (Prevailing Charge) and Part 2 (Interleaving Prevailing Charges).

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_GittinsIndex
import Definitions.Def_GittinsChargeInterleaving

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_ae_certificates_of_greedy_charge_interleaving
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
    (x : Fin k → S) (π : MarkovBanditPolicy k S)
    (hinterleaving :
      ∀ {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k},
        (∀ i, Antitone (H i)) →
        IsGreedyChargeStackInterleaving H astar →
        ∀ (a : ℕ → Fin k),
          Summable (fun n ↦ α ^ n * chargeStackInterleaving H a n) →
          Summable (fun n ↦ α ^ n * chargeStackInterleaving H astar n) →
          (∑' n : ℕ, α ^ n * chargeStackInterleaving H a n) ≤
            ∑' n : ℕ, α ^ n * chargeStackInterleaving H astar n) :
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
