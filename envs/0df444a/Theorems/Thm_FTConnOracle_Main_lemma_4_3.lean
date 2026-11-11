-- Prove2me | Theorems.Thm_FTConnOracle_Main_lemma_4_3
-- name    : FTConnOracle.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:44.262641+00:00
-- url     : https://prove2.me/theorems/6d77f628-337b-41fb-94f1-62c6bc4d99c7
-- title:
--   Lemma 4.3 (Cut amplification) — Q(S) symmetric ⟹ |δ_G(S)| = 0 or |δ_G(S)| > 3t²/4
-- statement:
--   Let $n\ge2$, let $B$ be a bipartite graph with left side $[n]$, right side $[r]$, all left degrees equal to $\ell\ge1$ and (4.1) for the parameter $t$. Let $G$ be a graph on $[n]$ and $S\subseteq[n]$. If the sketched cut matrix $Q(S)$ is symmetric, then
--
--   $$|\delta_G(S)|=0\quad\text{or}\quad|\delta_G(S)|>\tfrac34\,t^2.$$
--
--   Symmetry of $Q(S)$ thus amplifies "some edge crosses $S$" into "more than $3t^2/4$ edges cross $S$"; both oracles of §4 rest on this gap.
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - encoding: B as a bipartite graph / its r × n incidence matrix with 0/1 columns b_v; Q(S) an r × r matrix → B : Fin n → Finset (Fin r) (right neighbourhoods); b_v = col B v ∈ ℤ^r; Q(S) a Matrix (Fin r) (Fin r) ℤ, symmetric meaning Qᵀ = Q; reason: same objects; integer entries as in the paper
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 18 (PDF 20), Lemma 4.3

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-- Lemma 4.3 (cut amplification, p. 18): for a graph `G` on `[n]` and `S ⊆ [n]`, if the
sketched cut matrix `Q(S)` is symmetric then `|δ_G(S)| = 0` or `|δ_G(S)| > 3t²/4`. -/
theorem lemma_4_3 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hQ : (cutMatrix B G S).transpose = cutMatrix B G S) :
    (delta G S).card = 0 ∨ (3 / 4 : ℝ) * (t : ℝ) ^ 2 < ((delta G S).card : ℝ) := by sorry

end FTConnOracle.Main
