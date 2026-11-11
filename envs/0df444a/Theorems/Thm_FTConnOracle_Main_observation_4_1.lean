-- Prove2me | Theorems.Thm_FTConnOracle_Main_observation_4_1
-- name    : FTConnOracle.Main.observation_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:51.043684+00:00
-- url     : https://prove2.me/theorems/79886e25-e791-4a44-99b4-fff98c881751
-- title:
--   Observation 4.1 — Q(S)_{i,j} counts the paths i →B x →G y →B j with x ∈ S, y ∉ S
-- statement:
--   Let $n\ge2$, let $B$ be a bipartite graph with left side $[n]$ and right side $[r]$ (left degrees $\ell\ge1$, (4.1) for $t$), let $G$ be a graph on $[n]$ and $S\subseteq[n]$. For $i,j\in[r]$ let $P_{i,j}$ be the set of paths $i\xrightarrow{B}x\xrightarrow{G}y\xrightarrow{B}j$ with $x\in S$ and $y\in S^c$. Then
--
--   $$Q(S)_{i,j}=|P_{i,j}|.$$
--
--   The entries of the sketched cut matrix are thus path counts, which is how the lossless expansion of $B$ enters the cut-amplification argument.
--
--   **Formalization Note.** A path in $P_{i,j}$ is determined by its middle edge, so $P_{i,j}$ is the set of pairs $(x,y)$ with $x\in T_i\cap S$, $y\in T_j\setminus S$, $\{x,y\}\in E(G)$.
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - encoding: B as a bipartite graph / its r × n incidence matrix with 0/1 columns b_v; Q(S) an r × r matrix → B : Fin n → Finset (Fin r) (right neighbourhoods); b_v = col B v ∈ ℤ^r; Q(S) a Matrix (Fin r) (Fin r) ℤ, symmetric meaning Qᵀ = Q; reason: same objects; integer entries as in the paper
--   - encoding: paths i →B x →G y →B j → pairs (x, y) with i ∈ Γ(x), x ∈ S, {x, y} ∈ E(G), y ∉ S, j ∈ Γ(y) (pathSet); reason: such a path is determined by its middle edge (x, y); the count is the same
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 16 (PDF 18), Observation 4.1

import Mathlib
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-- Observation 4.1 (p. 16): for `i, j ∈ [r]`, the entry `Q(S)_{i,j}` of the sketched cut matrix
equals the number of paths `i →B x →G y →B j` with `x ∈ S` and `y ∈ Sᶜ`. -/
theorem observation_4_1 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (i j : Fin r) :
    cutMatrix B G S i j = ((pathSet B G S i j).card : ℤ) := by sorry

end FTConnOracle.Main
