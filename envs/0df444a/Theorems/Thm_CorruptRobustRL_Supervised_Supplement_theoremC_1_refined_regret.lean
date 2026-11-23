-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_Supplement_theoremC_1_refined_regret
-- name    : CorruptRobustRL.Supervised.Supplement.theoremC_1_refined_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:13:27.614028+00:00
-- url     : https://prove2.me/theorems/c128aba5-8cea-49f5-b0ae-688876314a11
-- title:
--   Theorem C.1 — refined tabular regret decomposition with explicit proof coefficients
-- statement:
--   Let $M$ be any finite nominal tabular MDP with horizon $H\ge1$. For each of $K$ episodes, let a randomized Markovian policy $\pi_k$, a Q-supervisor $\mathcal T_k$ and a model estimate satisfy Conditions C.1–C.3, with their source ranges and one common UCB visitation bound $\rho\ge1$. Define
--   $$A=\sum_{k=1}^K\mathbb E^{\pi_k}\sum_{h=1}^H\check{\operatorname{Err}}_{k;h}(x_h,a_h),\qquad B=\sum_{k=1}^K\mathbb E^{\pi_k}\sum_{h=1}^H\widetilde{\operatorname{Err}}_k(x_h,a_h),$$
--   where both errors are exactly (C.4)–(C.7), using truncated errors and the minimum positive stage gap. With $e=\exp(1)$ and $L=\sum_{k=1}^K(V^\star-V^{\pi_k})$, both bounds hold:
--   $$L\le(4+40eH\rho)A+81e^3H\rho B,\qquad L\le81e^3H\rho(A+B).$$
--   This companion theorem refines the generic regret decomposition into two gap-clipped error sums. It applies to arbitrary sequences meeting the abstract conditions, with no base-algorithm, nesting, empirical-count or concentration premise. It is not a step in the proof of the published goal Theorem 4.1.
--
--   **Formalization Note** The explicit coefficients come from the paper's concluding proof rather than a guessed hidden constant. The domain retains all finite tabular MDPs, all horizons at least one, tied optima and the all-optimal zero-loss case.
--
--   Differences from the source:
--   - encoding: stages h in [H] and randomized Markovian policies → zero-based stages, published finite mixtures and atom-wise concatenation; reason: finite state/action spaces and a finite horizon give finitely many relevant deterministic Markov policies; the original joint policy law is retained
--   - reading: p. 8 defines gap(x,a)=min_h gap_h(x,a) and the minimum non-zero gap as min over pairs (x,a) of gap(x,a), with no value specified when the set is empty → minimum of the strictly positive stage gaps, or zero in the all-optimal case; reason: PDF 70 explicitly defines gap_min as the minimum of gap_h(x,a)>0 over x,a,h (the convention of [SJ19]); the per-pair reading of p. 8 makes the lemma false (two states, H=2, a pair optimal at stage 2 with stage-1 gap ε, another pair with gaps 1/2; per-pair gap_min=1/2 clips every error 2ε to zero while the loss is ε), and the literal formula without 'non-zero' gives 0, a weaker statement implied by this one; when there are no positive gaps every policy has zero loss, so no source instance is excluded
--   - reading: the displayed regret bound uses an unspecified absolute multiplier → both the bound (4+40eHρ)A+81e³HρB and its consequence 81e³Hρ(A+B); reason: Lemma C.11 and the two change-of-measure displays on PDF 53–54 supply these explicit coefficients, with Hρ≥1
--   - encoding: an algorithm produces K episodes satisfying Conditions C.1–C.3 → arbitrary episode families indexed by Fin K and their witnessing model estimates; reason: the conclusion depends only on those outputs; every finite family can be emitted by an algorithm, and the empty sum case is included
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 45, Theorem C.1; concluding proof pp. 52–53

import Definitions.Def_CorruptRobustRL_Supervised_Supplement_ClippedErrors
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_EstimateRanges
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_VISupervisor
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_ValidBonus
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_Framework

namespace CorruptRobustRL.Supervised.Supplement

theorem theoremC_1_refined_regret
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (H : ℕ) (hH : 1 ≤ H) (hM : M.IsNominal)
    (K : ℕ) (T : Fin K → QSupervisor X A) (π : Fin K → Mixture X A)
    (m : Fin K → ModelEst X A) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hπ : ∀ k, (π k).IsMixture) (hframework : ∀ k, HasFramework M H (T k) (π k) ρ)
    (hranges : ∀ k, HasEstimateRanges H (m k))
    (hvi : ∀ k, IsVISupervisor H (T k) (m k))
    (hbonus : ∀ k, HasValidBonus M H (m k)) :
    let checkedSum := ∑ k, mixExpect M H (π k) (checkError M (m k) H)
    let squaredSum := ∑ k, mixExpect M H (π k) (fun _ x a => tildeError M (m k) H x a)
    let loss := ∑ k, (Vstar0 M H - mixValue M H (π k))
    loss ≤ (4 + 40 * Real.exp 1 * (H : ℝ) * ρ) * checkedSum +
      81 * (Real.exp 1) ^ 3 * (H : ℝ) * ρ * squaredSum ∧
    loss ≤ 81 * (Real.exp 1) ^ 3 * (H : ℝ) * ρ * (checkedSum + squaredSum) := by sorry

end CorruptRobustRL.Supervised.Supplement
