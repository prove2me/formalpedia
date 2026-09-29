-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_exists_tree_cotree
-- name    : AlgebraicCurve.CellDissection.exists_tree_cotree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/461fc9bd-4efc-5cfc-b12d-a0704f39d0d7
-- title:
--   Tree–cotree splitting of a cell dissection
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure, and let the space $\mathrm{Place}\ \mathbb{C}\ F$ of places carry a topology and a $\mathbb{C}$-charted-space structure. Let $\mathcal{D}$ be a `CellDissection` of $F$: finite index types $\iota C,\iota E,\iota V$ with decidable equality, cells `cell : ιC → Cell F` (a chart together with a radial region), a bijective side-labelling attaching to each boundary arc of each cell an edge index with a sign, an endpoint map `ends : ιE → ιV × ιV`, a vertex map `vert : ιV → Place ℂ F`, and the compatibility axioms of that structure (arc endpoints match the labelled vertices, the two sides of an edge are orientation-reversing reparametrisations of each other, the cells cover the space, and the intersection/connectedness conditions). Assume $\iota C$ is nonempty, `vert` is injective, every vertex index is an endpoint of some edge, and the Euler count $\#\iota V-\#\iota E+\#\iota C=2-2n$ holds, where $n=\dim_{\mathbb{C}}$ of `regularDifferentials ℂ F`, the submodule of $\Omega[F\!\restriction\!\mathbb{C}]$ of differentials $\omega$ such that for each place $v$ one has $\omega=f\cdot$`v.dCoord` with $f$ in the valuation subring of $v$. Write `Cside e s` for the cell on the $(e,s)$-side, obtained from the side bijection. Then there are edge subsets $\mathcal{T},\mathcal{T}^{s}\subseteq\iota E$ such that: for all vertices $u,v$ there is exactly one integral $1$-chain $c$ on the edges, vanishing off $\mathcal{T}$, whose boundary (head sums minus tail sums, heads being second components of `ends`) is $\delta_v-\delta_u$; for all cells $C,C'$ there is exactly one integral chain vanishing off $\mathcal{T}^{s}$ whose dual boundary (sums over edges with `Cside e true = D` minus those with `Cside e false = D`) is $\delta_{C'}-\delta_C$; $\mathcal{T}$ and $\mathcal{T}^{s}$ are disjoint; the complement of $\mathcal{T}\cup\mathcal{T}^{s}$ has exactly $2n$ elements; and any two vertices are joined by a walk using only edges of $\mathcal{T}$.
--
--   This is the tree–cotree splitting of the edge set of a cell decomposition of a compact Riemann surface: a spanning tree of the vertex–edge graph, a spanning tree of the dual cell–edge graph, and exactly $2g$ remaining edges, with the spanning-tree property expressed as unique solvability of the boundary equation for prescribed endpoints. It supplies the combinatorial input for the construction of a system of loops underlying the path-integral reciprocity statement [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_exists_tree_cotree.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.CellDissection.exists_tree_cotree
    {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F) [Nonempty 𝒟.ιC]
    (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v)
    (hEuler : (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
      = 2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    ∃ (𝒯 𝒯s : Finset 𝒟.ιE),
      (∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
        ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
          (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)) ∧
      (∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0)) ∧
      Disjoint 𝒯 𝒯s ∧
      (𝒯 ∪ 𝒯s)ᶜ.card = 2 * Module.finrank ℂ ↥(regularDifferentials ℂ F) ∧
      ∀ u v : 𝒟.ιV, Relation.ReflTransGen
        (fun a b => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v := by sorry
