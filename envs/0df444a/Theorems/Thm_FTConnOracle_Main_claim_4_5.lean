-- Prove2me | Theorems.Thm_FTConnOracle_Main_claim_4_5
-- name    : FTConnOracle.Main.claim_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:36:36.932782+00:00
-- url     : https://prove2.me/theorems/9956f115-4cbb-4eb1-9264-ce0c5c1343f5
-- title:
--   Claim 4.5 — the level decoder decides from the encoding, F and S alone whether G_i − F_i has an edge crossing S
-- statement:
--   Let $n\ge2$, let $B$ be a bipartite graph with left side $[n]$, right side $[r]$, all left degrees equal to $\ell\ge1$ and (4.1) for the parameter $t$, and let $D\ge0$ with $\frac34t^2>2D$. Let $G$ be a graph on $[n]$, $L\ge0$ and $M_1,\dots,M_L$ masks such that $M_{i+1}$ is $D$-good for $G_i$ for every $i<L$ (where $G_0=G$, $G_{i+1}=G_i\cap M_{i+1}$) and $G_L=\emptyset$. Let the encoding store $b_v$, $L$, $M_1,\dots,M_L$ and the level sketches $s_{i,u}=\sum_{(u,v)\in E(G_i)}b_v$ for $0\le i<L$. Let $F\subseteq E(G)$ and $S\subseteq[n]$, with $F_0=F$, $F_{i+1}=F_i\cap E(M_{i+1})$. Then for every $0\le i\le L$ the level decision procedure (backward recursion, Cases 1 and 2), run on the stored data, $F$ and $S$ only, satisfies
--
--   $$\text{it answers nonempty at level }i\iff G_i-F_i\text{ has an edge crossing }S.$$
--
--   At level $0$ this decides, for each cut $S$, whether $G-F$ has an edge crossing $S$, and hence recovers $\mathrm{cc}(G-F)$; it is the correctness core of the $\tilde O(n^{7/4})$-bit oracle (Theorem 4.4).
--
--   **Formalization Note.** "We can decide using only the encoding, the query $F$ and the set $S$" is stated as the correctness of the explicit procedure `levelDecide` of the proof, whose arguments are exactly the stored data, $D$, $F$ and $S$; a bare existence of a correct Boolean would be trivially true and is not what is stated.
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - generalization: masks M_1, …, M_L from the family M_n of Lemma 4.6; D = 2C n^{3/2}√(log n) and t = Θ(n^{3/4} log^{1/4} n) with 3t²/4 > 2D; L the first index with G_L = ∅ → any masks M_1, …, M_L with M_{i+1} D-good for G_i (i < L); any real D ≥ 0 and any t with 3t²/4 > 2D; any L with G_L = ∅ (⊥); reason: the proof uses only these properties; the source's choices satisfy them
--   - encoding: 'we can decide … using only the encoding, the query F, and the set S' → levelDecide (col B) L M (level sketches) D F S i = true ↔ δ_{G_i − F_i}(S) ≠ ∅, for the explicit backward recursion of the proof; reason: makes 'decide using only' precise: the procedure's inputs are the stored data, F and S; masks are passed as graphs, which their stored identifiers determine
--   - encoding: Test-Cut receives {(b_v, s_v)}_{v∈S} and {(b_u, b_v)}_{{u,v}∈F} → testCut takes the whole arrays b = col B and sk = nbrSketch B G but its value reads only b_u, sk_u for u ∈ S and b_v for endpoints v of F-edges; reason: Lean functions take whole arrays; the definition of testMatrix reads only the listed entries
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 24–25 (PDF 26–27), Claim 4.5 and its proof (Cases 1 and 2), with the encoding of §4.3 (p. 23, PDF 25)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander
import Definitions.Def_FTConnOracle_Main_Mask

namespace FTConnOracle.Main

/-- Claim 4.5 (p. 24): in the setting of §4.3 (`B` with left degrees `ℓ ≥ 1` and (4.1) for `t`,
`D ≥ 0` with `3t²/4 > 2D`, masks `M_1, …, M_L` with `M_{i+1}` `D`-good for `G_i` and `G_L = ∅`,
`F ⊆ E(G)`), for every `0 ≤ i ≤ L` the level decision procedure, which reads only the stored data
(`b_v`, `L`, the masks, the level sketches `s_{i,u}`), `F` and `S`, answers nonempty exactly when
`G_i − F_i` has an edge crossing `S`. -/
theorem claim_4_5 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (D : ℝ) (hD : 0 ≤ D)
    (htD : 2 * D < (3 / 4 : ℝ) * (t : ℝ) ^ 2) (G : SimpleGraph (Fin n)) (L : ℕ)
    (M : ℕ → SimpleGraph (Fin n)) (hgood : ∀ i, i < L → IsDGood D (M (i + 1)) (levelGraph G M i))
    (hL : levelGraph G M L = ⊥) (F : Finset (Sym2 (Fin n))) (hF : F ⊆ edges G)
    (S : Finset (Fin n)) (i : ℕ) (hi : i ≤ L) :
    levelDecide (col B) L M (fun j => nbrSketch B (levelGraph G M j)) D F S i = true ↔
      (delta (removeEdges (levelGraph G M i) (levelFail F M i)) S).Nonempty := by sorry

end FTConnOracle.Main
