-- Prove2me | Theorems.Thm_CoDecompFO_Supplement_theorem_5_70
-- name    : CoDecompFO.Supplement.theorem_5_70
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:53:26.062216+00:00
-- url     : https://prove2.me/theorems/979a79af-885b-4dbc-83a5-99f5b3516298
-- title:
--   Theorem 5.70 (corrected: $\beta:[2(\ell-m)]\to\lim\mathcal T$, $\pi_{a*}S\in\mathrm{Strat}_m(G_a,\pi_a\beta)$) — the co-decomposition $\mathcal T_*S$ and the canonical map into its limit
-- statement:
--   Let $\mathcal T=(T,\{G_a\},\{g^e_t\})$ be a tree co-decomposition with projections $\pi_a:\lim\mathcal T\to G_a$, let $0\le m\le\ell$, $\beta:[2(\ell-m)]\to\lim\mathcal T$ and $S\in\mathrm{Strat}_m(\lim\mathcal T,\beta)$, and let $\pi_{a*}S\in\mathrm{Strat}_m(G_a,\pi_a\circ\beta)$ be the projection of $S$. With the induced morphisms of strategies
--
--   $$(g^e_t,g^e_{t*}):(G_t,\pi_t\beta,\pi_{t*}S)\to(G_e,\pi_e\beta,\pi_{e*}S),$$
--
--   the tuple $\mathcal T_*S=(T,\{\pi_{a*}S\},\{(g^e_t,g^e_{t*})\})$ is a co-decomposition valued in the total category of strategies, and there is a canonical map $(\lim\mathcal T,\beta,S)\to\lim(\mathcal T_*S)$. Precisely:
--
--   1. the legs $(\pi_a,\mathrm{id})$ make $(\lim\mathcal T,\beta,S)$ a cone over $\mathcal T_*S$;
--   2. every arrow $(g^e_t,g^e_{t*})$ is an epimorphism of $\mathrm{Strat}^\sigma_m$;
--   3. $\mathcal T_*S$ has a limit in $\mathrm{Strat}^\sigma_m$;
--   4. there is a unique map from $(\lim\mathcal T,\beta,S)$ to that limit commuting with the legs.
--
--   This is the strategy analogue of Lemma 4.12 for co-decompositions: a global strategy induces a matching family of local strategies.
--
--   **Formalization Note** The diagram, cones and limits are those of the shape of $T$ (nodes, edges, incidence arrows), stated explicitly.
--
--   Differences from the source:
--   - correction: β : [2ℓ − m] → lim T → β : Fin (2 * (ℓ - m)) → T.Lim; reason: Strat_m(G, β) is defined only for β : [2(ℓ−m)] → G (¶5.9, ¶5.33); the printed index makes S ∈ Strat_m(lim T, β) ill-typed
--   - correction: π_a∗S ∈ Strat_m(lim T, π_a ∘ β) → StratObj.push (π_a) m S, an m-strategy on G_a over π_a ∘ β; reason: π_a ∘ β is an assignment into G_a, so the printed type is ill-formed; the same sentence says "the projection of S to (G_a, π_a ∘ β)"
--   - reading: T ∗ S is a co-decomposition valued in the total category of strategies → the legs (π_a, 𝟙) form a cone over T ∗ S, and every arrow (g^e_t, g^e_{t∗}) is an epimorphism; reason: a co-decomposition has epimorphic arrows (¶1.6); the stronger of the two readings (footnote 1 defines a plain diagram), and the cone is what the proof uses
--   - reading: there is a canonical map (lim T, β, S) → lim(T ∗ S) → T ∗ S has a limit, and there is a unique map to it commuting with the legs; reason: the proof obtains the map as the unique limit arrow
--   - encoding: a diagram indexed by T and its limit → TreeDiagram with explicit IsCone / IsLimit over nodes, edges and incidence arrows; reason: the barycentric subdivision has no composable non-identity arrows, so this is the same diagram and the same limit
--   - encoding: the total category of strategies → StratTot σ m (2 * (ℓ - m)), morphisms written over maps of positions; reason: same hom-sets, as for Theorem 5.53
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Theorem 5.70, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_CoDecompFO_Supplement_StarStrat

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open CategoryTheory

/-- **Theorem 5.70** (Bumpus, Gomes, Larios-Jones, Turner, *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, p.36), corrected as the text dictates: for a tree co-decomposition
`T`, an assignment `β : [2(ℓ−m)] → lim T` and an `m`-strategy `S ∈ Strat_m(lim T, β)`, the projections
`π_{a*} S ∈ Strat_m(G_a, π_a ∘ β)` with the induced morphisms `(g^e_t, g^e_{t*})` form a co-decomposition `T ∗ S`
valued in the total category of strategies, and there is a canonical map `(lim T, β, S) → lim(T ∗ S)`.

The conclusion has four parts: (i) the legs `(π_a, 𝟙)` make `(lim T, β, S)` a cone over `T ∗ S`; (ii) every
arrow `(g^e_t, g^e_{t*})` of `T ∗ S` is an epimorphism of `Strat^σ_m`, so `T ∗ S` is a co-decomposition (epic
arrows, ¶1.6) and not only a diagram; (iii) `T ∗ S` has a limit; (iv) there is a unique map from
`(lim T, β, S)` to that limit commuting with the legs.

**Formalization Note** The page prints "β : [2ℓ − m] → lim T" and "π_{a*}S ∈ Strat_m(lim T, π_a ∘ β)"; an
`m`-strategy is relative to `β : [2(ℓ−m)] → G` (¶5.9, ¶5.33), and the projection of `S` lives over
`(G_a, π_a ∘ β)`, as the same sentence says. The total category is `StratTot σ m (2(ℓ−m))`. -/
theorem theorem_5_70 {σ : Sig} (T : CoDecomp σ) (ℓ m : ℕ) (hm : m ≤ ℓ) (β : Fin (2 * (ℓ - m)) → T.Lim)
    (S : StratObj T.Lim m) :
    (starDiagram T m β S).IsCone (limStrat T m β S) (starNodeLeg T m β S) (starEdgeLeg T m β S) ∧
    (∀ e, Epi ((starDiagram T m β S).left e) ∧ Epi ((starDiagram T m β S).right e)) ∧
    ∃ (L : StratTot σ m (2 * (ℓ - m))) (legN : ∀ t, L ⟶ (starDiagram T m β S).node t)
      (legE : ∀ e, L ⟶ (starDiagram T m β S).edge e),
      (starDiagram T m β S).IsLimit L legN legE ∧
      ∃! u : limStrat T m β S ⟶ L,
        (∀ t, u ≫ legN t = starNodeLeg T m β S t) ∧ ∀ e, u ≫ legE e = starEdgeLeg T m β S e := by sorry

end Supplement

end CoDecompFO
