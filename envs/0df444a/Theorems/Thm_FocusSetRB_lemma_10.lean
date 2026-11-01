-- Prove2me | Theorems.Thm_FocusSetRB_lemma_10
-- name    : FocusSetRB.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:19:24.957994+00:00
-- url     : https://prove2.me/theorems/18d943b0-334d-44a6-9563-be46f01538df
-- title:
--   Lemma 10, eq. (93), p.39 — the LP relaxation bounds the optimal reward
-- statement:
--   Let $0<\alpha<1$, $N\ge1$ and $k=\alpha N\in\mathbb N$. Let $R^{\mathrm{rel}}$ be the optimal value of (LP) and $R^*(N,S_0)$ the optimal reward of the $N$-armed restless bandit problem (RB), the supremum of the liminf average reward over all history-dependent randomized policies that pull exactly $\alpha N$ arms at every step. Then for every initial state vector $S_0$,
--
--   $$
--   R^{\mathrm{rel}}\ge R^*(N,S_0).
--   $$
--
--   This is the upper bound through which every optimality gap of the paper is controlled: $R^*(N,S_0)-R^-(\pi,S_0)\le R^{\mathrm{rel}}-R^-(\pi,S_0)$.
--
--   Differences from the source:
--   - encoding: R*(N,S₀) the optimal value of (RB) over policies that may be randomized and use the whole history → supremum of R⁻ over history-dependent randomized policies whose every action vector pulls exactly k = αN arms; reason: the class the paper describes on p.5; the budget (1a) holds at every step
--   - encoding: αN an integer, N arms → k : ℕ with (k : ℝ) = α·N and N ≥ 1; reason: the paper assumes αN is an integer (p.5); an N-armed problem has N ≥ 1
--   - encoding: R^rel the optimal value of (LP) → the real sSup of the (LP) objective over the feasible set; reason: for 0 < α < 1 the feasible set is nonempty and compact, so the supremum is the maximum
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 10, eq. (93), p.39

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_HRPolicy

namespace FocusSetRB

/-- **Lemma 10 (LP relaxation), eq. (93), p.39** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4). Let `R^rel` be the optimal value
of the linear program (LP), and let `R*(N, S₀)` be the optimal reward of the `N`-armed restless
bandit problem (RB). Then `R^rel ≥ R*(N, S₀)`.

**Formalization Note.** (RB) has budget `αN = k` with `0 < α < 1`, `N ≥ 1`, and objective the
liminf average reward `R⁻`; `R*(N, S₀)` is the supremum of `R⁻(π, S₀)` over all
history-dependent randomized policies satisfying (1a) at every step. `R^rel` is the supremum of
the (LP) objective over its feasible set. No unichain assumption is needed or made. -/
theorem lemma_10 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {N k : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) = α * N) (S0 : Fin N → S) :
    Rstar M N k S0 ≤ Rrel M α := by sorry

end FocusSetRB
