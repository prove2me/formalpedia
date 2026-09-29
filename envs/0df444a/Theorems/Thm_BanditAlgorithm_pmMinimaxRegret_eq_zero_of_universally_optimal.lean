-- Prove2me | Theorems.Thm_BanditAlgorithm_pmMinimaxRegret_eq_zero_of_universally_optimal
-- name    : BanditAlgorithm.pmMinimaxRegret_eq_zero_of_universally_optimal
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:15:39.812518+00:00
-- url     : https://prove2.me/theorems/571aca95-4593-4a2e-b997-23e9117c893d
-- title:
--   A universally optimal action has zero partial-monitoring minimax regret
-- statement:
--   Let $G$ be a finite partial-monitoring game. Suppose there is an action $a$ whose loss is no larger than the loss of any action $b$ on every outcome $i$: $L_{a i} \le L_{b i}$. Then, for every horizon $n$,
--
--   $$
--   R_n^*(G)=0.
--   $$
--
--   Indeed, always playing $a$ achieves zero worst-case regret, while comparison with $a$ makes every policy's worst-case regret nonnegative. This lemma isolates the decision-theoretic part of the zero-regret case and is reusable independently of the cell geometry.
--
--   **Formalization Note** The statement includes the discrete-signal measurability assumptions needed to construct and evaluate the deterministic constant policy.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Section 37.8, Theorem 37.22, printed p. 503 (PDF p. 511), constant-policy conclusion; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.pmMinimaxRegret_eq_zero_of_universally_optimal
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a : Fin k)
    (ha : ∀ b : Fin k, ∀ i : Fin d, G.L a i ≤ G.L b i) :
    ∀ n : ℕ, pmMinimaxRegret G n = 0 := by
  sorry
