-- Prove2me | Theorems.Thm_ARGFContract_Hardness_Supplement_lemma_B_5
-- name    : ARGFContract.Hardness.Supplement.lemma_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:54.247808+00:00
-- url     : https://prove2.me/theorems/019c7f9f-9168-41a7-9fb5-15be09704e0d
-- title:
--   Lemma B.5 (used in the proof of Theorem 9) — Within-cluster value stability
-- statement:
--   Let $p_i\in\mathbb R$ be competencies of agents $E=\{1,\dots,N\}$ and let $f:2^E\to\mathbb R$ satisfy Assumption B.1 with a constant $L\ge0$: for all distinct $i,j$ and all $B\subseteq E\setminus\{i,j\}$,
--
--   $$|f(B\cup\{i\})-f(B\cup\{j\})|\le L\,|p_i-p_j| .$$
--
--   Let $E=C_1\cup\dots\cup C_K$ be disjoint clusters with gaps $\epsilon_a\ge0$, i.e. $|p_i-p_j|\le\epsilon_a$ for all $i,j\in C_a$. If $S,S'\subseteq E$ have the same cluster profile, $|S\cap C_a|=|S'\cap C_a|$ for every $a$, then
--
--   $$|f(S)-f(S')|\ \le\ L\sum_{a=1}^K|S\cap C_a|\,\epsilon_a .$$
--
--   This lemma converts the gap bound into a bound on value differences and is the key estimate behind Theorem 9.
--
--   **Formalization Note** Clusters are the classes of a labelling $E\to\{1,\dots,K\}$; empty clusters are allowed.
--
--   Differences from the source:
--   - generalization: f ∈ ARGF (setting of Appendix B.3) → f an arbitrary real set function satisfying Assumption B.1 and the gap bound; reason: the lemma's own hypotheses are B.1 and the gap bound; ARGFs are a special case
--   - generalization: a partition N = C_1 ∪ … ∪ C_K → a labelling cl : Fin N → Fin K whose classes may be empty; reason: an empty cluster contributes 0 to both sides; partitions are a special case
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Lemma B.5, p. 41

import Mathlib
import Definitions.Def_ARGFContract_Hardness_Supplement_Prefixes

open Finset

namespace ARGFContract.Hardness.Supplement

/-- Lemma B.5 (within-cluster value stability), p. 41. Under Assumption B.1 with constant
`L` and the gap bound `|p_i − p_j| ≤ ε_a` on every cluster `C_a`, two sets with the same
cluster profile satisfy `|f(S) − f(S')| ≤ L ∑_a |S ∩ C_a| ε_a`. -/
theorem lemma_B_5 {n K : ℕ} (p : Fin n → ℝ) (f : Finset (Fin n) → ℝ) (L : ℝ)
    (cl : Fin n → Fin K) (ε : Fin K → ℝ)
    (hL : LipschitzCompetency L p f) (hε : ∀ a, 0 ≤ ε a)
    (hgap : HasCompetencyGaps p cl ε) (S S' : Finset (Fin n))
    (hprof : ∀ a, (S ∩ block cl a).card = (S' ∩ block cl a).card) :
    |f S - f S'| ≤ L * ∑ a, ((S ∩ block cl a).card : ℝ) * ε a := by sorry

end ARGFContract.Hardness.Supplement
