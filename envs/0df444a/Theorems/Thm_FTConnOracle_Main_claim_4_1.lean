-- Prove2me | Theorems.Thm_FTConnOracle_Main_claim_4_1
-- name    : FTConnOracle.Main.claim_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:33:03.02116+00:00
-- url     : https://prove2.me/theorems/551dcace-2c3a-4b7f-ae92-dd654c6612bd
-- title:
--   Claim 4.1 — Test-Cut returns 1 on every empty surviving cut
-- statement:
--   Let $n\ge2$, let $B$ be a bipartite graph with left side $[n]$, right side $[r]$, all left degrees equal to $\ell\ge1$ and (4.1) for the parameter $t$, and let $G$ be a graph on $[n]$ with sketches $b_v$, $s_v$. For every $F\subseteq E(G)$ and $S\subseteq[n]$,
--
--   $$\delta_{G-F}(S)=\emptyset\ \Longrightarrow\ \text{Test-Cut}\big(S,F,\{(b_v,s_v)\}_{v\in S},\{(b_u,b_v)\}_{\{u,v\}\in F}\big)=1.$$
--
--   Together with Lemma 4.4 this makes Test-Cut a one-sided certificate: an output $0$ proves the surviving cut nonempty.
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - encoding: B as a bipartite graph / its r × n incidence matrix with 0/1 columns b_v; Q(S) an r × r matrix → B : Fin n → Finset (Fin r) (right neighbourhoods); b_v = col B v ∈ ℤ^r; Q(S) a Matrix (Fin r) (Fin r) ℤ, symmetric meaning Qᵀ = Q; reason: same objects; integer entries as in the paper
--   - encoding: Test-Cut receives {(b_v, s_v)}_{v∈S} and {(b_u, b_v)}_{{u,v}∈F} → testCut takes the whole arrays b = col B and sk = nbrSketch B G but its value reads only b_u, sk_u for u ∈ S and b_v for endpoints v of F-edges; reason: Lean functions take whole arrays; the definition of testMatrix reads only the listed entries
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 19 (PDF 21), Claim 4.1

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-- Claim 4.1 (p. 19): for every `F ⊆ E(G)` and `S ⊆ [n]`, Test-Cut, run on `S`, `F`, the
sketches `(b_v, s_v)` of `G` and the sketches of the endpoints of `F`, returns `1` whenever
`δ_{G−F}(S) = ∅`. -/
theorem claim_4_1 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hF : F ⊆ edges G) (S : Finset (Fin n)) (hcut : delta (removeEdges G F) S = ∅) :
    testCut (col B) (nbrSketch B G) S F = true := by sorry

end FTConnOracle.Main
