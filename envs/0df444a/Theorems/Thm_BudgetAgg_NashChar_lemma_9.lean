-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_9
-- name    : BudgetAgg.NashChar.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:47.23633+00:00
-- url     : https://prove2.me/theorems/5fb47a2c-78a2-4e71-b3f7-c4b64f852154
-- title:
--   Lemma 9, p. 33 — a continuous, group-strategyproof, efficient mechanism keeps its outcome and the critical sets at the key profile P∗
-- statement:
--   Let $f$ be a mechanism for Leontief utilities that is continuous, group-strategyproof and efficient (that is, $f(P)$ is efficient at $P$ for every profile $P$). Fix any profile $P$ and write $q=f(P)$. Let $P^*$ be the profile whose $i$-th peak is the key peak of $p_i$ at $q$:
--   $$p^*_{i,j}=\begin{cases}p_{i,j}/p_i(T_{q,i}) & j\in T_{q,i},\\ 0 & \text{otherwise.}\end{cases}$$
--   Then
--   1. the outcome does not change: $f(P^*)=f(P)=q$;
--   2. the critical sets do not change: $T^*_{q,i}=T_{q,i}$ for every $i\in N$, where $T^*_{q,i}$ is computed with the peak $p^*_i$.
--
--   For example, $p_i=(0.1,0.2,0.3,0.4)$ and $q=(0.1,0.1,0.6,0.2)$ give $T_{q,i}=\{2,4\}$ and $p^*_i=(0,1/3,0,2/3)$. Lemma 9 is the first equality in the proof of Theorem 3.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. The profile $P^*$ is pinned down by requiring $(P^*_i) = $ `starPeak (P i) (f P)` for every $i$; the existence of such a profile (i.e. that each key peak is a distribution) is part of the conclusion. Continuity is `Continuous` on the subtype $(\Delta^m)^n$. The hypothesis is efficiency, as printed, not core fair share.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 33, Lemma 9 (proof pp. 33–35)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 9, p. 33: moving to the page's key profile preserves the outcome and critical sets. -/
theorem lemma_9 {n m : ℕ} [NeZero n] [NeZero m]
    (f : Mechanism n m) (hf_cont : Continuous f) (hf_gsp : IsGroupSP f)
    (hf_eff : ∀ P, IsEfficient P (f P)) (P : Profile n m) :
    ∃ Ps : Profile n m,
      (∀ i, (Ps i).1 = starPeak (P i) (f P).1) ∧
      f Ps = f P ∧
      (∀ i, crit (Ps i) (f P).1 = crit (P i) (f P).1) := by sorry

end BudgetAgg.NashChar
