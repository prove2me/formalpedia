-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_lemma_4
-- name    : ArcKayles192.PSPACE.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:03:35.347098+00:00
-- url     : https://prove2.me/theorems/cf221842-2bc7-4b6e-80ee-2fde42b24f66
-- title:
--   Lemma 4 (Sprague–Grundy): $\mathrm{sg}(G_1\uplus\cdots\uplus G_h)=\mathrm{sg}(G_1)\oplus\cdots\oplus\mathrm{sg}(G_h)$
-- statement:
--   Let $h\ge 0$ and let $G_1,\dots,G_h$ be simple graphs on vertex types $W_1,\dots,W_h$, with positions $S_1,\dots,S_h$. Let $G_1\uplus\cdots\uplus G_h$ be their disjoint union on $\Sigma_iW_i$, with position $S_1\uplus\cdots\uplus S_h$. Then
--   $$\mathrm{sg}(G_1\uplus\cdots\uplus G_h,\ S_1\uplus\cdots\uplus S_h)=\mathrm{sg}(G_1,S_1)\oplus\cdots\oplus\mathrm{sg}(G_h,S_h),$$
--   where $\oplus$ is bitwise exclusive or on $\mathbb N$ and the empty xor is $0$.
--
--   This is the Sprague–Grundy theorem for Arc Kayles, due to Sprague (1935) and Grundy (1939). Claims 7–10 use it to split $G_\varphi$ into components.
--
--   Differences from the source:
--   - encoding: a position is a graph; isolated vertices are removed automatically (p.3) → a position is a finite set S of remaining vertices of an ambient simple graph G, the current graph being G[S]; isolated vertices stay in S; reason: an isolated vertex carries no move, so outcomes and values are unchanged; every finite graph H is the position (H, all vertices), and every position is the finite graph G[S]
--   - generalization: a family G_1, …, G_h (h ≥ 1 implicit) → h ≥ 0; for h = 0 both sides are 0; reason: the case h ≥ 1 is the source's statement; h = 0 adds only the empty union
--   - encoding: G_1 ⊎ ⋯ ⊎ G_h and a_1 ⊕ ⋯ ⊕ a_h → sigmaGraph on the sigma type Σ i : Fin h, W i; xor as List.foldr (· ^^^ ·) 0 over List.ofFn; reason: ⊕ is associative and commutative with unit 0, so the fold order is immaterial
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.3, Lemma 4 (citing [14, 8])

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

namespace ArcKayles192.PSPACE

/-- **Lemma 4** (Sprague–Grundy, p.3). For every finite family of graphs `G₁, …, G_h` (here with
positions `S_i`), the value of the disjoint union is the bitwise xor of the values:
`sg(G₁ ⊎ ⋯ ⊎ G_h) = sg(G₁) ⊕ ⋯ ⊕ sg(G_h)`. The empty union (`h = 0`) has value `0`. -/
theorem lemma_4 (h : ℕ) {W : Fin h → Type*} [∀ i, DecidableEq (W i)]
    (G : ∀ i, SimpleGraph (W i)) (S : ∀ i, Finset (W i)) :
    sg (sigmaGraph G) (Finset.univ.sigma S) =
      (List.ofFn fun i => sg (G i) (S i)).foldr (· ^^^ ·) 0 := by sorry

end ArcKayles192.PSPACE
