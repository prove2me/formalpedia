-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values
-- name    : AlgebraicCurve.CellDissection.kirchhoff_and_jump_formula_of_arc_values
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/fc055c3d-396d-58b6-902c-29b3be76f3be
-- title:
--   Kirchhoff's law and the word formula for arc jumps
-- statement:
--   Fix a field $F$ over $\mathbb{C}$ whose space of places $\mathrm{Place}\,\mathbb{C}\,F$ carries a topology and a $\mathbb{C}$-charted structure, and a cell dissection $\mathcal{D}$ of $F$, with finite index types $\iota C$ of cells, $\iota E$ of edges, $\iota V$ of vertices, each cell $C$ having $N$ boundary arcs indexed by $\mathrm{Fin}\,(\mathcal{D}.\mathrm{cell}\,C).R.N$, the assignment $\mathcal{D}.\mathrm{side}$ sending an arc $(C,k)$ to an edge together with an orientation bit, bijectively on all arcs (so $\mathcal{D}.\mathrm{arcOf}$ is its inverse), and $\mathcal{D}.\mathrm{ends}\,e=(\text{tail},\text{head})$. Let $\mathbb{A}$ be an additive commutative group and let $A,B$ assign to each arc an element of $\mathbb{A}$, $I,J:\iota E\to\mathbb{A}$, $\mathrm{rot}\,C$ a self-map of the arc indices of $C$, $\mathcal{T},\mathcal{T}s$ finite sets of edges, $Z:\iota E\to\iota E\to\mathbb{Z}$, and $\mathrm{wd}$ a bijection from $\mathbb{Z}/m$ ($m\neq 0$) onto the oriented arcs $(e,\pm)$ with $e\notin\mathcal{T}s$. Write $\mathrm{startV}(e,+)=\text{tail}(e)$, $\mathrm{endV}(e,+)=\text{head}(e)$ and conversely for $(e,-)$, and for $e\notin\mathcal{T}s$ let $\mathrm{pe}\,e\,e'$ be the signed number of letters of the word $\mathrm{wd}$ carrying the edge $e'$ (sign $+1$ for a positive copy, $-1$ for a negative one) whose index $i$ lies strictly between the positions of $(e,+)$ and $(e,-)$, in the sense that $i\neq \mathrm{wd}^{-1}(e,+)$ and $(i-\mathrm{wd}^{-1}(e,+)).\mathrm{val}<(\mathrm{wd}^{-1}(e,-)-\mathrm{wd}^{-1}(e,+)).\mathrm{val}$. Assume: $B\,p-A\,p=\pm I e$ on each arc $p$ according to the orientation bit of $\mathcal{D}.\mathrm{side}$ at $p$, with $e$ its edge; each $\mathrm{rot}\,C$ is bijective; the arc $\mathrm{rot}\,C\,k$ starts where arc $k$ ends, and $A\langle C,\mathrm{rot}\,C\,k\rangle=B\langle C,k\rangle$; $J e=B(\mathcal{D}.\mathrm{arcOf}(e,+))-A(\mathcal{D}.\mathrm{arcOf}(e,-))$ and also $J e=A(\mathcal{D}.\mathrm{arcOf}(e,+))-B(\mathcal{D}.\mathrm{arcOf}(e,-))$; distinct arcs of one cell have distinct starting vertices; $J$ vanishes on $\mathcal{T}s$; every $\mathbb{Z}$-valued, and every $\mathbb{A}$-valued, edge function $f$ satisfying Kirchhoff's law at each vertex $w$ (the sum of $f$ over edges with head $w$ equals the sum over edges with tail $w$) obeys $f e=\sum_{j\in\mathcal{T}^{c}}Z j e\cdot f j$; consecutive letters of the word meet, $\mathrm{endV}(\mathrm{wd}\,i)=\mathrm{startV}(\mathrm{wd}(i+1))$, and the cells of these two letters are joined by a list of cells forming a chain for the relation "glued along some edge $g\in\mathcal{T}s$ having that common vertex as an endpoint"; and each $\mathrm{pe}\,e$ satisfies Kirchhoff's law. The conclusion is threefold: $J$ satisfies Kirchhoff's law at every vertex; for every $j\notin\mathcal{T}s$, $J j=-\sum_{l\in(\mathcal{T}\cup\mathcal{T}s)^{c}}\mathrm{pe}\,j\,l\cdot\sum_{e}Z l e\cdot I e$; and for every edge $f$ there are integers $n l$ with $J f=\sum_{l\in(\mathcal{T}\cup\mathcal{T}s)^{c}}n l\cdot\sum_{e}Z l e\cdot I e$.
--
--   This is the purely combinatorial core of the period computation on a cell dissection: boundary values of a multivalued object on the arcs of the dissection determine edge jumps which are closed for the vertex (Kirchhoff) relations and hence integral combinations of the cycle sums $\sum_e Z l e\cdot I e$ attached to the complement of a spanning set $\mathcal{T}$, with an explicit coefficient given by counting letters of the boundary word. It is used by [`AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues`](thm.html#AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues) to write a path integral as an integral combination of periods and residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.kirchhoff_and_jump_formula_of_arc_values
    {F : Type u} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F) (𝔸 : Type) [AddCommGroup 𝔸]
    (A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸) (I J : 𝒟.ιE → 𝔸)
    (rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N)
    (𝒯 𝒯s : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (m : ℕ) [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) :
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
      ∑ i ∈ Finset.univ.filter
          (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
            (i - wd.symm ⟨(e, true), he⟩).val <
              (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
        (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
    (∀ p, B p - A p =
      if (𝒟.side p.1 p.2).2 then I (𝒟.side p.1 p.2).1 else -I (𝒟.side p.1 p.2).1) →
    (∀ C, Function.Bijective (rot C)) →
    (∀ C k, endV (𝒟.side C k) = startV (𝒟.side C (rot C k))) →
    (∀ C k, A ⟨C, rot C k⟩ = B ⟨C, k⟩) →
    (∀ e, J e = B (𝒟.arcOf (e, true)) - A (𝒟.arcOf (e, false))) →
    (∀ e, J e = A (𝒟.arcOf (e, true)) - B (𝒟.arcOf (e, false))) →
    (∀ C, Function.Injective fun k : Fin (𝒟.cell C).R.N => startV (𝒟.side C k)) →
    (∀ e ∈ 𝒯s, J e = 0) →
    (∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j) →
    (∀ f : 𝒟.ιE → 𝔸,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j) →
    (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
        cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
            ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
          (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) →
    (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) →
    (∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e) ∧
    (∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
      J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, pe j hj l • ∑ e, Z l e • I e) ∧
    ∀ f : 𝒟.ιE, ∃ n : 𝒟.ιE → ℤ, J f = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, n l • ∑ e, Z l e • I e := by sorry
