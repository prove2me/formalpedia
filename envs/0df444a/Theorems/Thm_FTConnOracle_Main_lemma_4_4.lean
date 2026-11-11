-- Prove2me | Theorems.Thm_FTConnOracle_Main_lemma_4_4
-- name    : FTConnOracle.Main.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:56.649329+00:00
-- url     : https://prove2.me/theorems/ac4760b7-3df5-4b77-8526-82c66082928a
-- title:
--   Lemma 4.4 — Test-Cut = 1 ⟹ the surviving cut is empty or has more than 3t²/4 edges
-- statement:
--   Let $n\ge2$, let $B$ be a bipartite graph with left side $[n]$, right side $[r]$, all left degrees equal to $\ell\ge1$ and (4.1) for the parameter $t$, and let $G$ be a graph on $[n]$ with sketches $b_v$, $s_v$. Fix any $S\subseteq[n]$ and $F\subseteq E(G)$. Then
--
--   $$\text{Test-Cut}\big(S,F,\{(b_v,s_v)\}_{v\in S},\{(b_u,b_v)\}_{\{u,v\}\in F}\big)=1\ \Longrightarrow\ |\delta_{G-F}(S)|=0\ \text{ or }\ |\delta_{G-F}(S)|>\tfrac34t^2.$$
--
--   This is cut amplification read through the sketches of $G$ and the query: the decoder never sees $G-F$, yet Test-Cut certifies the same gap for it.
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - encoding: B as a bipartite graph / its r × n incidence matrix with 0/1 columns b_v; Q(S) an r × r matrix → B : Fin n → Finset (Fin r) (right neighbourhoods); b_v = col B v ∈ ℤ^r; Q(S) a Matrix (Fin r) (Fin r) ℤ, symmetric meaning Qᵀ = Q; reason: same objects; integer entries as in the paper
--   - encoding: Test-Cut receives {(b_v, s_v)}_{v∈S} and {(b_u, b_v)}_{{u,v}∈F} → testCut takes the whole arrays b = col B and sk = nbrSketch B G but its value reads only b_u, sk_u for u ∈ S and b_v for endpoints v of F-edges; reason: Lean functions take whole arrays; the definition of testMatrix reads only the listed entries
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 19 (PDF 21), Lemma 4.4

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-- Lemma 4.4 (p. 19): fix `S ⊆ [n]` and `F ⊆ E(G)`. If Test-Cut returns `1`, then
`|δ_{G−F}(S)| = 0` or `|δ_{G−F}(S)| > (3/4) t²`. -/
theorem lemma_4_4 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (F : Finset (Sym2 (Fin n))) (hF : F ⊆ edges G)
    (htest : testCut (col B) (nbrSketch B G) S F = true) :
    (delta (removeEdges G F) S).card = 0 ∨
      (3 / 4 : ℝ) * (t : ℝ) ^ 2 < ((delta (removeEdges G F) S).card : ℝ) := by sorry

end FTConnOracle.Main
