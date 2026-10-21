-- Prove2me | Theorems.Thm_AllocationIndices_Precedence_residual_index_le
-- name    : AllocationIndices.Precedence.residual_index_le
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:14.483112+00:00
-- url     : https://prove2.me/theorems/7892b508-ad20-4789-870b-d9698dedc429
-- title:
--   p. 98 — after the first FI* stage the index of the remaining family does not exceed $\nu(\mathscr F)$, and strictly for a suitable stopping time
-- statement:
--   Let $\mathscr F$ be a family of $n$ ordinary jobs on a single machine with precedence constraints (no circuits), no arrivals and no preemption: job $i$ yields the reward $V_i e^{-\gamma C_i}$ at its completion time $C_i$, $V_i > 0$, $\gamma > 0$, and the service times $\sigma_i > 0$ are independent. Let $B$ be the set of jobs already completed, $\nu(\mathscr F)$ the index (4.15) of the family, and $(\pi, \sigma)$ the first stage of a modified forwards induction policy, i.e. any stage (possibly adaptive) attaining the supremum in (4.15). Let $\mathscr G$ be what remains of $\mathscr F$ at time $\sigma$: the family whose completed jobs are those of $B$ together with the jobs completed during the stage. Then, with probability one, if $\mathscr G$ still has an uncompleted job,
--   $$\nu(\mathscr G) \le \nu(\mathscr F).$$
--   Moreover the inequality is strict for a suitable choice of the stage: there is a first stage $(\pi, \sigma)$ of an FI\* policy (the book: $\sigma$ characterized as the first time that, under $\pi$, $\nu(\mathscr G) < \nu(\mathscr F)$) such that, with probability one, if $\mathscr G$ still has an uncompleted job,
--   $$\nu(\mathscr G) < \nu(\mathscr F).$$
--
--   This is one of the ingredients of the book's scheme for proving that an optimal policy may begin with the first stage of an FI\* policy: rewards of the remaining family that a competing policy collects earlier are worth no more than at rate $\nu(\mathscr G) \le \nu(\mathscr F)$.
--
--   **Formalization Note** The non-strict inequality is stated for every FI\* first stage. The book's strictness concerns one particular choice of $\sigma$ (the first time at which $\nu(\mathscr G) < \nu(\mathscr F)$; with ties, other FI\* stages may stop while $\nu(\mathscr G) = \nu(\mathscr F)$), so it is stated as the existence of an FI\* first stage after which the inequality is strict. Both statements hold almost surely in the service times; $\nu$ is defined only when an uncompleted job remains, hence the guard.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.6 p. 98 (the sentence following Eq. (4.20))

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

theorem residual_index_le {n : ℕ} (F : JobFamily n) (B : Finset (Fin n)) (p : Stage n)
    (hp : IsFIStarStage F B p) :
    (∀ᵐ ω ∂serviceLaw F, B ∪ p.jobsDone B ω ≠ Finset.univ →
      familyIndex F (B ∪ p.jobsDone B ω) ≤ familyIndex F B) ∧
    ∃ q : Stage n, IsFIStarStage F B q ∧
      ∀ᵐ ω ∂serviceLaw F, B ∪ q.jobsDone B ω ≠ Finset.univ →
        familyIndex F (B ∪ q.jobsDone B ω) < familyIndex F B := by sorry

end AllocationIndices.Precedence
