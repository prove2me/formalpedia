-- Prove2me | Theorems.Thm_CrossLearnCB_UCB1CL_eq_4
-- name    : CrossLearnCB.UCB1CL.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:15.337273+00:00
-- url     : https://prove2.me/theorems/0e001622-6a5d-4732-9ae1-6d2222512cb9
-- title:
--   Eq. (4), p. 19 — X_i(c_(1)) + ··· + X_i(c_(j)) ≤ m_i(c_(j)) + 1 for contexts ordered by decreasing gap
-- statement:
--   Fix an arm $i$, a horizon $T$, a context sequence and an arm sequence, and a set $S$ of contexts. Enumerate $S$ as $c_{(1)},\dots,c_{(|S|)}$ so that the gaps are positive and non-increasing,
--   $$\Delta_i(c_{(1)})\ge\Delta_i(c_{(2)})\ge\cdots\ge\Delta_i(c_{(|S|)})>0,$$
--   so that $m_i(c_{(1)})\le\cdots\le m_i(c_{(|S|)})$, where $m_i(c)=8\log T/\Delta_i(c)^2$. Let $X_i(c)$ be the number of rounds $t\le T$ with $c_t=c$, $I_t=i$ and $\tilde\tau_{i,t}(S)\le m_i(c)$, where $\tilde\tau_{i,t}(S)$ counts the pulls of arm $i$ in contexts of $S$ before round $t$. Then for every $j$,
--   $$X_i(c_{(1)})+X_i(c_{(2)})+\cdots+X_i(c_{(j)})\le m_i(c_{(j)})+1 .$$
--
--   This system of inequalities is the combinatorial core of the bound on the pre-regret (Lemma 3): weighting the $j$-th inequality by $\Delta_i(c_{(j)})-\Delta_i(c_{(j+1)})$ and summing bounds the pre-regret incurred on one clique of a clique cover.
--
--   **Formalization Note.** The page prints the right-hand sides as $m_i(c_{(j)})$; the statement holds only with $m_i(c_{(j)})+1$, because $\tilde\tau$ takes the values $0,1,\dots,\lfloor m\rfloor$ while it is at most $m$, i.e. up to $\lfloor m\rfloor+1$ rounds (with $m$ not an integer the printed first row fails). The inequality is pathwise: it holds for every arm and context sequence, and for any set $S$, not only a clique of $G_i$. The enumeration is an injective map $e:\{0,\dots,n-1\}\to[C]$ with image $S$; Lean indices are 0-based. Positive gaps are required because Lean's $8\log T/0$ is $0$ rather than $+\infty$.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 19, Eq. (4); X_i(c), τ̃_{i,t}(r) p. 18

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model

open MeasureTheory ProbabilityTheory

namespace CrossLearnCB.UCB1CL

/-- System (4), p. 19, with the right-hand sides `m_i(c_(j)) + 1`: for contexts `e 0, …, e (n-1)`
enumerating `S` in order of non-increasing positive gap, the counts `X_i(c_(k))` for `k ≤ j`
sum to at most `m_i(c_(j)) + 1`. Pathwise, for any arm and context sequences. -/
theorem eq_4 {K C : ℕ} (gap : Fin K → Fin C → ℝ) (ctx : ℕ → Fin C) (I : ℕ → Fin K) (T : ℕ)
    (i : Fin K) (S : Finset (Fin C)) {n : ℕ} (e : Fin n → Fin C)
    (he : Function.Injective e) (hrange : Set.range e = ↑S)
    (hpos : ∀ k, 0 < gap i (e k))
    (hord : ∀ k l, k ≤ l → gap i (e l) ≤ gap i (e k)) (j : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), (cliqueX gap ctx I T i S (e k) : ℝ))
      ≤ mThr T (gap i (e j)) + 1 := by sorry

end CrossLearnCB.UCB1CL
