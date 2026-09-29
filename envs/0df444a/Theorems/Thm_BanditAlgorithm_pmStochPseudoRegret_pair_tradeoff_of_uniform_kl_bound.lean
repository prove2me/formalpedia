-- Prove2me | Theorems.Thm_BanditAlgorithm_pmStochPseudoRegret_pair_tradeoff_of_uniform_kl_bound
-- name    : BanditAlgorithm.pmStochPseudoRegret_pair_tradeoff_of_uniform_kl_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:53:14.217635+00:00
-- url     : https://prove2.me/theorems/74bc19be-9c93-424d-8871-90231a6c4496
-- title:
--   Two-environment partial-monitoring regret tradeoff under a uniform KL bound
-- statement:
--   Consider two stochastic partial-monitoring environments $u_a,u_b$ with optimal comparator actions $a,b$. Suppose actions outside a designated set $N$ have gap at least $\varepsilon/2$ in both environments, while for every action in $N$ the two suboptimality gaps sum to $\Delta>0$. If the KL divergence between the two induced history laws is finite and at most $D$, then for every policy there is a nonnegative expected outside-action count $x$ such that
--
--   $$
--   \frac{\varepsilon}{2}x+\frac{n\Delta}{8}e^{-D}\le R_n(\pi,u_a,a)+R_n(\pi,u_b,b).
--   $$
--
--   This uniform-KL form separates the geometric regret accounting from whichever information bound is available and is directly suited to square-root lower bounds.
--
--   **Formalization Note** The proof applies the finite-history Bretagnolle–Huber inequality to a threshold event determined by actions in $N$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), proof of Theorem 37.12, Eqs. (37.8)–(37.10), printed pp. 490–491 (PDF pp. 498–499), and Theorem 37.14 proof sketch, printed p. 492 (PDF p. 500); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality_finite_typeStar

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

theorem BanditAlgorithm.pmStochPseudoRegret_pair_tradeoff_of_uniform_kl_bound
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (ua ub : Fin d → ℝ) (hua : ua ∈ stdSimplex ℝ (Fin d))
    (hub : ub ∈ stdSimplex ℝ (Fin d)) (a b : Fin k)
    (N : Finset (Fin k)) (ε D Δ : ℝ)
    (hΔ : 0 < Δ) (hΔε : Δ ≤ ε)
    (haopt : ∀ c : Fin k, 0 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a)
    (hbopt : ∀ c : Fin k, 0 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b)
    (houta : ∀ c : Fin k, c ∉ N → ε / 2 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a)
    (houtb : ∀ c : Fin k, c ∉ N → ε / 2 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b)
    (hinside : ∀ c : Fin k, c ∈ N →
      (pmExpectedLoss G ua c - pmExpectedLoss G ua a) +
        (pmExpectedLoss G ub c - pmExpectedLoss G ub b) = Δ)
    (hKLfin : klDiv (pmStochMeasure G π ua hua n) (pmStochMeasure G π ub hub n) ≠ ⊤)
    (hKL : (klDiv (pmStochMeasure G π ua hua n) (pmStochMeasure G π ub hub n)).toReal ≤ D) :
    ∃ x : ℝ, 0 ≤ x ∧
      ε / 2 * x + (n : ℝ) * Δ / 8 * Real.exp (-D) ≤
        pmStochPseudoRegret G π ua hua n a + pmStochPseudoRegret G π ub hub n b := by
  sorry
