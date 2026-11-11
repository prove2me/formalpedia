-- Prove2me | Theorems.Thm_FTConnOracle_Main_lemma_4_5
-- name    : FTConnOracle.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:35:51.800232+00:00
-- url     : https://prove2.me/theorems/ac9f43aa-afc8-436d-b6a3-55ac9a6e2eeb
-- title:
--   Lemma 4.5 — the cut decoder (4.6) returns empty exactly when δ_{G−F}(S) = ∅
-- statement:
--   Let $n\ge2$ and let $f$ be an integer with $1\le f\le\binom n2$. Set $\varepsilon=1/(4f^{1/5})$ and $t=\lceil\sqrt{8\varepsilon f}\rceil$ as in (4.5), and assume $t<n/4$. Let $B$ be a bipartite graph with left side $[n]$, right side $[r]$, all left degrees equal to $\ell\ge1$ and (4.1) for $t$. Let $G$ be a graph on $[n]$ with sketches $b_v$, $s_v$, and let $H$ be an $\varepsilon$-cut sparsifier of $G$ (4.4). For every $F\subseteq E(G)$ with $|F|\le f$ and every $S\subseteq[n]$, the cut decoder (4.6) — which returns empty iff Test-Cut$(S,F,\{(b_v,s_v)\}_{v\in S},\{(b_u,b_v)\}_{\{u,v\}\in F})=1$ and $c_H(S)\le(1+\varepsilon)|\delta_F(S)|$ — satisfies
--
--   $$\text{the cut decoder returns empty}\iff\delta_{G-F}(S)=\emptyset.$$
--
--   Applied to every cut, this recovers $\mathrm{cc}(G-F)$ from $\langle H,\{(s_v,b_v)\}\rangle$ and $F$; it is the correctness core of the $\tilde O(f^{2/5}n)$-bit oracle (Theorem 4.2).
--
--   **Formalization Note.** $H$ is given by its nonnegative weights `w : Sym2 (Fin n) → ℝ`.
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
--   - generalization: H the (1 + ε)-cut sparsifier of the encoding: a reweighted subgraph of G with O(n/ε²) edges from Theorem 4.3, weights rounded (footnote 7) → H any weighted graph on [n] with nonnegative real weights satisfying (4.4) with ε; reason: the proof uses only (4.4); the encoding's sparsifier satisfies it, so the statement specializes to the source's
--   - reading: 'H is an (1 + ε)-cut sparsifier as above' → IsCutSparsifier G w ε, i.e. (4.4) with the ε of (4.5); reason: the paper's (4.4) calls this an ε-cut sparsifier, and the proof of Lemma 4.5 applies (4.4) with this ε
--   - encoding: Test-Cut receives {(b_v, s_v)}_{v∈S} and {(b_u, b_v)}_{{u,v}∈F} → testCut takes the whole arrays b = col B and sk = nbrSketch B G but its value reads only b_u, sk_u for u ∈ S and b_v for endpoints v of F-edges; reason: Lean functions take whole arrays; the definition of testMatrix reads only the listed entries
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 20 (PDF 22), Lemma 4.5, with the construction (4.5), (4.6) of §4.2

import Mathlib
import Definitions.Def_FTConnOracle_Main_Oracle
import Definitions.Def_FTConnOracle_Main_Expander
import Definitions.Def_FTConnOracle_Main_Sparsifier

namespace FTConnOracle.Main

/-- Lemma 4.5 (p. 20): in the setting of §4.2 (`1 ≤ f ≤ C(n,2)`, `ε = 1/(4f^{1/5})`,
`t = ⌈√(8εf)⌉ < n/4`, `B` with left degrees `ℓ ≥ 1` and (4.1) for `t`, `H` an `ε`-cut sparsifier
of `G`), for every `F ⊆ E(G)` with `|F| ≤ f` and every `S ⊆ [n]`, the cut decoder (4.6) returns
empty exactly when `δ_{G−F}(S) = ∅`. -/
theorem lemma_4_5 {n r ℓ : ℕ} (hn : 2 ≤ n) (f : ℕ) (hf1 : 1 ≤ f) (hf2 : f ≤ n.choose 2)
    (ht : (tF f : ℝ) < (n : ℝ) / 4) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ (tF f)) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (hH : IsCutSparsifier G w (epsF f)) (F : Finset (Sym2 (Fin n))) (hF : F ⊆ edges G)
    (hFf : F.card ≤ f) (S : Finset (Fin n)) :
    cutDecoder f w (col B) (nbrSketch B G) S F = true ↔ delta (removeEdges G F) S = ∅ := by sorry

end FTConnOracle.Main
