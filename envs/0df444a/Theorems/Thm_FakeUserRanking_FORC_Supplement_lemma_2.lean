-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_Supplement_lemma_2
-- name    : FakeUserRanking.FORC.Supplement.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:34:19.54019+00:00
-- url     : https://prove2.me/theorems/c0c71017-4d08-44f7-8846-1d5d38c328e0
-- title:
--   Lemma 2, p. 21 — under FAR with δ = 1/(nT), the event E of (8)–(9) has probability at least 1 − δ²/(nT)
-- statement:
--   **Lemma 2 (concentration inequality).** Let $n,T\ge1$, let $F$ be the fakeness budget, which FAR is given, and let $\delta=1/(nT)$. For every instance and every fake-user policy with fakeness budget $F$,
--
--   $$\mathbb P(\mathcal E)\;\ge\;1-\frac{\delta^2}{nT},$$
--
--   where $\mathcal E=\bigcap_{i\in[n],t\in[T]}\mathcal E_{i,t}$ is the event of (8)–(9): at the end of every round $t\in[T]$, every product $i$ satisfies $r_{i,t}-w_{i,t}\le\mu_i\le r_{i,t}+w_{i,t}$, with FAR's average reward $r_{i,t}$ and the window $w_{i,t}$ of (9), including its branch $\max(1,\sqrt{\log(2nT/\delta)}+F)$ when $\eta_{i,t}=0$.
--
--   With $\delta=1/(nT)$ the bound reads $1-(nT)^{-3}$. It is the first step of the proof of Theorem 2: off $\mathcal E$ the regret is at most $\delta^2$, see (10)–(12).
--
--   **Formalization Note** Products and positions are indexed from $0$ in Lean: Lean product $i$ is the paper's product $i+1$, and likewise for positions. Lean round index $t$ is the paper's round $t+1$; "the end of round $t$" is the state after the first $t$ rounds, $t=0$ being the initial state. The probability is over the run of FAR against the policy, as in the published model. The statement holds for every resolution `tb`, `fb` of Algorithm 2's unspecified choices.
--
--   Differences from the source:
--   - encoding: products, positions and rounds are numbered from 1 → products and positions are `Fin n` and rounds are trajectory indices, all numbered from 0; reason: a relabelling; every instance of the paper corresponds to exactly one Lean instance
--   - generalization: FAR as defined, with GraphRankSelect's tie-break among the smallest η, on an instance satisfying (1) μ₁ > … > μ_n → every instance (no ordering of μ) and every pair of functions tb, fb, including tie-breaks that do not pick a member of the tied set; reason: the concentration argument (C.2, pp. 48–50) never uses the ranking rule or the ordering of μ; FAR proper is the special case where tb respects Algorithm 2 and μ is decreasing
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 21, Lemma 2; event E, (8)–(9), pp. 20–21; proof in Appendix C.2, pp. 48–50

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
import Definitions.Def_FakeUserRanking_FORC_Supplement_EventE

namespace FakeUserRanking.FORC.Supplement

/-- Lemma 2 (Concentration Inequality), p. 21: under FAR with `δ = 1/(nT)`, against every fake-user
policy within the budget `F` that FAR is given, the event `E` of (8)–(9) has probability at least
`1 − δ²/(nT)`. -/
theorem lemma_2 (n T F : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T) (inst : Instance n)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) :
    1 - farDelta n T ^ 2 / ((n : ℝ) * T) ≤
      prob inst P (far n T F tb fb) T (eventE inst T F tb fb) := by sorry

end FakeUserRanking.FORC.Supplement
