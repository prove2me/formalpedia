-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_lemma_14
-- name    : BudgetAgg.NashChar.Supplement.lemma_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:05:37.045316+00:00
-- url     : https://prove2.me/theorems/a875d827-b8df-49e9-a78e-3ff34d034a43
-- title:
--   Lemma 14 (used in the proof of Theorem 4) — Leximin-Leontief efficiency iff every funded alternative is critical for some agent
-- statement:
--   Let $P=(p_1,\dots,p_n)$ be a profile and $q\in\Delta_m$ a distribution. Call $j$ **critical** for agent $i$ at $q$ if $p_{i,j}>0$ and $q_j/p_{i,j}=\min_{k:p_{i,k}>0}q_k/p_{i,k}$ (Definition 12). With **Leximin-Leontief preferences**, $q$ is efficient if and only if every alternative it funds is critical for some agent:
--
--   $$q\ \text{efficient}\iff\forall j\ \big(q_j>0\Rightarrow\exists i:\ j\in T_{q,i}\big).$$
--
--   It shows that efficiency is the same for Leximin-Leontief preferences as for Leontief utilities (Lemma 1), and it is used for Proposition 6 and so for Theorem 4.
--
--   **Formalization Note** $n,m\ge1$ (the paper's positive integers). Efficiency is Definition 1 with the relations $\succeq^{lex}$, $\succ^{lex}$; critical sets are the published minimum-ratio `crit`.
--
--   Differences from the source:
--   - encoding: agents N = [n], alternatives M = [m], 1-based → Fin n, Fin m (0-based); distributions and peaks are points of stdSimplex ℝ (Fin m); reason: relabelling only; every instance corresponds
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 40, Lemma 14 (proof sketch p. 40)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_Leximin

namespace BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Lemma 14, p. 40: with Leximin-Leontief preferences, `q` is efficient iff every
alternative it funds is critical (minimum ratio) for some agent. -/
theorem lemma_14 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) :
    IsLexEfficient P q ↔ ∀ j, 0 < q.1 j → ∃ i, j ∈ crit (P i) q.1 := by sorry

end BudgetAgg.NashChar.Supplement
