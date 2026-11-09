-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_lemma5
-- name    : DirectedHamiltonicity.Main.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:37.01948+00:00
-- url     : https://prove2.me/theorems/7f2d0aef-694c-4cab-ae93-5b3ffa459301
-- title:
--   Lemma 5 — the path polynomial is nonzero with probability at least $(1-\delta)^{n-1}$
-- statement:
--   Let $G=(V,A)$ be a simple loopless directed graph on $n$ vertices with distinct vertices $s,t$, no arcs entering $s$ and no arcs leaving $t$, and let $d\ge2$, $\delta=1/(1+(2^d-1)^2)$. Draw independent sets $S_{uv}\subseteq[d]$, $uv\in A$, with $\Pr[S_{uv}=\varnothing]=\delta$ and $\Pr[S_{uv}=S]=(1-\delta)/(2^d-1)$ for nonempty $S$, and let
--   $$f(z)=\sum_{P\in\mathcal P_{s,t}(G)}\prod_{uv\in P}\Bigl(\sum_{\ell\in S_{uv}}z_{v\ell}\Bigr)\in\mathbb F_2[z_{v\ell}:v\ne s,\ \ell\in[d]].$$
--   If $G$ has a Hamiltonian path from $s$ to $t$, then
--   $$\Pr[f(z)\ne0]\ \ge\ (1-\delta)^{n-1},$$
--   where $f(z)\ne0$ means that $f$ is a nonzero polynomial.
--
--   By the coefficient identity of §3, $f\ne0$ exactly when some group selection has an odd number of Hamiltonian paths, so this lemma is equivalent to Proposition 3.
--
--   Differences from the source:
--   - encoding: G = (V, A) a simple loopless directed graph on n vertices with distinct s, t, no arcs entering s and none leaving t, and d ≥ 2 (standing assumptions of §2, PDF p.4) → an adjacency relation adj on a finite type V with n = |V|, and the hypotheses s ≠ t, ∀ v, ¬adj v v, ∀ u, ¬adj u s, ∀ v, ¬adj t v, 2 ≤ d; reason: a simple digraph is exactly a relation; the standing assumptions are written as binders; [d] is Fin d
--   - encoding: probability over the independent random sets S_uv ⊆ [d] with Pr[S_uv = ∅] = δ and Pr[S_uv = S] = (1−δ)/(2^d−1) for S ≠ ∅ → copyProb d E = Σ over joint outcomes S satisfying E of ∏_{uv} copySetProb d (S uv); reason: the product law of finitely many independent finite random variables, written as an explicit finite sum
--   - encoding: a directed (multi)graph with arc set E(H); a Hamiltonian path from s to t as a path visiting every vertex once → Multidigraph V E (tail, head : E → V, arcs labelled by E); a Hamiltonian path is a sequence of n−1 arcs e_0,…,e_{n−2} with tail e_i = v_i, head e_i = v_{i+1}, v_0 = s, v_{n−1} = t, and v injective; reason: a bijection with the source paths; parallel copies of an arc give distinct paths, as in the source
--   - encoding: indeterminates z_{vℓ} for v ≠ s and ℓ ∈ [d] → MvPolynomial ({v // v ≠ s} × Fin d) (ZMod 2); reason: the same polynomial ring; a factor for an arc entering s would be 0, and no such arc exists by hypothesis
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.6 / printed p.5, Lemma 5 (setting PDF p.4 / printed p.3; proof PDF pp.6–7 / printed pp.5–6)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies

namespace DirectedHamiltonicity.Main

open Multidigraph

/-- Lemma 5, PDF p.6 / printed p.5. Let `G` (adjacency `adj`) be a simple loopless digraph on `n`
vertices with distinct `s, t`, no arc entering `s` and no arc leaving `t`, and let `d ≥ 2`. If `G` has
a Hamiltonian path from `s` to `t`, then, for independent random sets `S_uv ⊆ [d]` with
`Pr[S_uv = ∅] = δ` and `Pr[S_uv = S] = (1 − δ)/(2^d − 1)` (`S ≠ ∅`), the path polynomial `f(z)` over
`𝔽₂` is a nonzero polynomial with probability at least `(1 − δ)^{n−1}`. -/
theorem lemma5 {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (s t : V) (hst : s ≠ t) (hloop : ∀ v, ¬ adj v v) (hs : ∀ u, ¬ adj u s) (ht : ∀ v, ¬ adj t v)
    (d : ℕ) (hd : 2 ≤ d) (hham : ((ofAdj adj).hamPaths s t).Nonempty) :
    (1 - delta d) ^ (Fintype.card V - 1) ≤
      copyProb (adj := adj) d (fun S => pathPoly adj s t S ≠ 0) := by sorry

end DirectedHamiltonicity.Main
