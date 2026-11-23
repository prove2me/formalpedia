-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_Supplement_lemmaC_11_clipped_localized_regret
-- name    : CorruptRobustRL.Supervised.Supplement.lemmaC_11_clipped_localized_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:12:52.211158+00:00
-- url     : https://prove2.me/theorems/2765a8f9-9d26-4470-879f-9c5488abe1f5
-- title:
--   Lemma C.11 — clipped localized regret via fictitious trajectories
-- statement:
--   Let $M$ be any finite nominal tabular MDP with horizon $H\ge1$. Let $\pi_k$ be a probability mixture of deterministic Markov policies, Q-supervised by a confidence-admissible Q-supervisor $\mathcal T_k$ with UCB policy $u_k$. Let the model estimate $(\widehat r_k,\widehat p_k,b_k)$ have the source ranges, obey both VI inequalities of Condition C.2 and optimal-value bonus validity C.3. Write $\check{\operatorname{Err}}_{k;h}$ and $\widetilde{\operatorname{Err}}_k$ for (C.6)–(C.7), and $e=\exp(1)$. Then
--   $$V^\star-V^{\pi_k}\le4\mathbb E^{\pi_k}\sum_{h=1}^H\check{\operatorname{Err}}_{k;h}(x_h,a_h)
--   +40e\sum_{h=1}^H\mathbb E^{\pi_k\oplus_h u_k}\sum_{\tau=h}^H\check{\operatorname{Err}}_{k;\tau}(x_\tau,a_\tau)
--   +81e^3\sum_{h=1}^H\mathbb E^{\pi_k\oplus_h u_k}\sum_{\tau=h}^H\widetilde{\operatorname{Err}}_k(x_\tau,a_\tau).$$
--   This is the full per-episode fictitious-trajectory decomposition supporting Theorem C.1. It requires no visitation-ratio premise and retains all three terms.
--
--   **Formalization Note** All expectations, optimal values and concatenations are those of the published base MDP. The horizon-one case, tied optima and the all-optimal case remain in scope.
--
--   Differences from the source:
--   - encoding: stages h in [H] and randomized Markovian policies → zero-based stages, published finite mixtures and atom-wise concatenation; reason: finite state/action spaces and a finite horizon give finitely many relevant deterministic Markov policies; the original joint policy law is retained
--   - reading: p. 8 defines gap(x,a)=min_h gap_h(x,a) and the minimum non-zero gap as min over pairs (x,a) of gap(x,a), with no value specified when the set is empty → minimum of the strictly positive stage gaps, or zero in the all-optimal case; reason: PDF 70 explicitly defines gap_min as the minimum of gap_h(x,a)>0 over x,a,h (the convention of [SJ19]); the per-pair reading of p. 8 makes the lemma false (two states, H=2, a pair optimal at stage 2 with stage-1 gap ε, another pair with gaps 1/2; per-pair gap_min=1/2 clips every error 2ε to zero while the loss is ε), and the literal formula without 'non-zero' gives 0, a weaker statement implied by this one; when there are no positive gaps every policy has zero loss, so no source instance is excluded
--   - reading: the first expectation writes (x,a), and the tilde error has a stage subscript → the first expectation uses (x_h,a_h), and the tilde error is the stage-independent (C.7); reason: (C.6)–(C.7), PDF 46, and the proof on PDF 76–77 fix these suppressed indices
--   - reading: the lemma abbreviates admissible supervisors and valid bonuses → all governing Q-supervision, model ranges and Conditions C.2–C.3 are explicit premises; reason: the context of C.11 and its cited C.4/C.9 uses these premises; no visitation-ratio condition is added
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 52, Lemma C.11; proof pp. 75–76

import Definitions.Def_CorruptRobustRL_Supervised_Supplement_ClippedErrors
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_EstimateRanges
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_VISupervisor
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_ValidBonus
import Definitions.Def_CorruptRobustRL_Supervised_Supplement_Framework

namespace CorruptRobustRL.Supervised.Supplement

theorem lemmaC_11_clipped_localized_regret
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (H : ℕ) (hH : 1 ≤ H) (hM : M.IsNominal)
    (T : QSupervisor X A) (π : Mixture X A) (m : ModelEst X A)
    (hπ : π.IsMixture) (hT : T.IsQSupervisor H) (hadm : T.IsAdmissible M H)
    (hsup : IsQSupervised H π T) (hranges : HasEstimateRanges H m)
    (hvi : IsVISupervisor H T m) (hbonus : HasValidBonus M H m) :
    Vstar0 M H - mixValue M H π ≤
      4 * mixExpect M H π (checkError M m H) +
      40 * Real.exp 1 * ∑ h ∈ Finset.range H,
        mixExpect M H (concatMix π h T.ucb)
          (fun τ x a => if h ≤ τ then checkError M m H τ x a else 0) +
      81 * (Real.exp 1) ^ 3 * ∑ h ∈ Finset.range H,
        mixExpect M H (concatMix π h T.ucb)
          (fun τ x a => if h ≤ τ then tildeError M m H x a else 0) := by sorry

end CorruptRobustRL.Supervised.Supplement
