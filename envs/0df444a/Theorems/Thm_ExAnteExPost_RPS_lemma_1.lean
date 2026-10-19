-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_lemma_1
-- name    : ExAnteExPost.RPS.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:37.145055+00:00
-- url     : https://prove2.me/theorems/c01e2a4b-285e-4107-aeec-a8d9513bd8e2
-- title:
--   Lemma 1, p. 11 — in iteration t < ⌈m/n⌉ an agent weakly prefers her good to every good still unallocated
-- statement:
--   Fix an instance with $n \ge 1$ agents, a favorite-good choice rule and an admissible decomposition rule, and run Algorithm 1 for its $\lceil m/n \rceil$ stages from $M^1 = M$. Consider any history $(B^1, \dots, B^{\lceil m/n \rceil})$ of stage allocations that occurs with positive probability, and write $M^{t+1} = M \setminus \bigcup_{s \le t} \bigcup_i B^s_i$ for the goods unallocated after $t$ iterations. Then for every iteration $t < \lceil m/n \rceil$, every agent $i$, every good $g_{i,t} \in B^t_i$ and every good $g^* \in M^{t+1}$,
--   $$v_i(g_{i,t}) \ge v_i(g^*) .$$
--
--   This is the comparison that drives Lemma 2: the good an agent receives in one iteration is worth at least as much to her as anything another agent receives later.
--
--   **Formalization Note.** Histories are lists indexed from $0$: entry $t$ is the paper's iteration $t+1$, so the paper's condition $t < \lceil m/n \rceil$ reads $t + 1 < \lceil m/n \rceil$, and "unallocated after the iteration" means outside the first $t+1$ entries. Only histories of positive probability are considered: Theorem 1 allows terms of weight zero, and such a term can give an agent a good she never ate, for which the lemma fails.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 11, Lemma 1

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- Lemma 1, p. 11. Stages are indexed from `0`: the entry `t` of a history is the paper's
iteration `t + 1`, so `t + 1 < ⌈m/n⌉` is the paper's `t < ⌈m/n⌉`, and the goods outside the first
`t + 1` stage allocations form `M^{t+1}` (paper indexing). Every agent weakly prefers a good she
receives in such an iteration to every good still unallocated after it, along every history drawn
with positive probability. -/
theorem lemma_1 [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D) :
    ∀ e ∈ rpsHist pick D (stages N G) univ, 0 < e.1 →
      ∀ (t : ℕ) (B : IntAlloc N G), t + 1 < stages N G → e.2[t]? = some B →
        ∀ i, ∀ g ∈ B i, ∀ g' ∉ allocatedGoods (e.2.take (t + 1)), I.v i g' ≤ I.v i g := by sorry
end ExAnteExPost.RPS
