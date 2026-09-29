-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_exists_polygonWord
-- name    : AlgebraicCurve.CellDissection.exists_polygonWord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/ce2154c4-141d-587a-b9d4-f94a00f4a59f
-- title:
--   Polygon boundary word of a cut cell dissection
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure, the space $\mathrm{Place}\ \mathbb{C}\ F$ carrying a topology and a $\mathbb{C}$-charted structure, and let $\mathcal{D}$ be a `CellDissection` of $F$, with cell, edge and vertex index types $\iota C,\iota E,\iota V$, side assignment `side` a bijection from incident pairs $(C,k)$ onto $\iota E\times\mathrm{Bool}$, end-pairs `ends` and vertex map `vert`. Assume `vert` injective. Let $\mathcal{T}s\subseteq\iota E$ be a finite set of edges, and write $\mathrm{Cside}(e,s)$ for the cell whose side is the oriented edge $(e,s)$. The hypothesis on $\mathcal{T}s$ is that for any two cells $C,C'$ there is exactly one $\mathbb{Z}$-valued function $c$ on edges, vanishing off $\mathcal{T}s$, whose dual boundary $\sum_{\mathrm{Cside}(e,\mathrm{true})=D}c_e-\sum_{\mathrm{Cside}(e,\mathrm{false})=D}c_e$ equals $[D=C']-[D=C]$ for every cell $D$; assume also that some edge lies outside $\mathcal{T}s$. Put $\mathrm{startV}(e,s)$, $\mathrm{endV}(e,s)$ equal to the two components of $\mathcal{D}.\mathrm{ends}(e)$, in that order when $s=\mathrm{true}$ and reversed otherwise, let $L$ be the set of oriented edges $(e,s)$ with $e\notin\mathcal{T}s$, and $m=\#L$. The conclusion asserts $m\neq 0$ together with a bijection $wd:\mathbb{Z}/m\to L$ such that: (i) for each $i$, $\mathrm{endV}$ of the letter $wd(i)$ equals $\mathrm{startV}$ of $wd(i+1)$, and there is a list of cells beginning with the cell carrying $wd(i)$, ending with the cell carrying $wd(i+1)$, consecutive members of which are the two cells flanking some $g\in\mathcal{T}s$ (in either orientation) with that common vertex an endpoint of $g$; and (ii) for each $e\notin\mathcal{T}s$, writing $\alpha_e,\beta_e$ for the positions of $(e,\mathrm{true}),(e,\mathrm{false})$ and $p_e$ for the $\mathbb{Z}$-chain on edges given by summing $\pm1$ (the sign being the orientation bit of the letter) over the positions $i\neq\alpha_e$ with $(i-\alpha_e).\mathrm{val}<(\beta_e-\alpha_e).\mathrm{val}$, one has, for every vertex $w$, $\sum_{(\mathrm{ends}\,f).2=w}p_e(f)=\sum_{(\mathrm{ends}\,f).1=w}p_e(f)$.
--
--   This is the combinatorial polygon-schema step: cutting a cell dissection open along the edge set $\mathcal{T}s$, which by hypothesis behaves like a spanning tree of the dual graph (unique $\mathcal{T}s$-supported $1$-chain joining any two cells), leaves a single polygon whose boundary is one cyclic word in the remaining oriented edges, with consecutive letters meeting at a vertex through $\mathcal{T}s$-adjacent cells, and with each chord chain $p_e$ a cycle for the vertex boundary map. It is used by [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw), where the corner conditions make glued primitives continuous and the Kirchhoff closedness turns the chord chains into loops.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_exists_polygonWord.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.CellDissection.exists_polygonWord
    {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F)
    (hvert : Function.Injective 𝒟.vert)
    (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
        fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
      ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (hL : ∃ e : 𝒟.ιE, e ∉ 𝒯s) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let L := {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}
    let m := Fintype.card L
    ∃ (_ : NeZero m) (wd : ZMod m ≃ L),
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (Cside (wd i).1.1 (wd i).1.2) ∧
          cs.getLast? = some (Cside (wd (i + 1)).1.1 (wd (i + 1)).1.2) ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            ((Cside g true = D ∧ Cside g false = D') ∨
             (Cside g true = D' ∧ Cside g false = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s),
        let αe : ZMod m := wd.symm ⟨(e, true), he⟩
        let βe : ZMod m := wd.symm ⟨(e, false), he⟩
        let pe : 𝒟.ιE → ℤ := fun e' =>
          ∑ i ∈ Finset.univ.filter
              (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
            (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
        ∀ w : 𝒟.ιV,
          (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f) := by sorry
