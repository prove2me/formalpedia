-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives
-- name    : AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/4b483ef1-3204-5ff1-b40c-7d9cf59449c4
-- title:
--   Kirchhoff's law and the boundary-word formula for primitive jumps
-- statement:
--   Let $F$ be a field over $\mathbb{C}$ with $\Omega[F/\mathbb{C}]$ free of rank one and all residue fields of places finite over $\mathbb{C}$ (`IsCurveOver`), essentially of finite type, whose place space $\mathrm{Place}\,\mathbb{C}\,F$ is a Hausdorff analytic manifold charted by $\mathbb{C}$; assume $F$ contains a transcendental $x$ with $F$ finite over $\mathbb{C}(x)$, and that for every $f \neq 0$ and every place $v$ the function $z \mapsto \mathrm{evalAt}\,((\mathrm{extChartAt}\,v)^{-1} z)\,f$ is meromorphic at $\mathrm{extChartAt}\,v\,v$ with meromorphic order $v.\mathrm{ord}\,f$. Let $\mathcal{D}$ be a cell dissection of $F$ with injective vertex map, $\kappa$ a finite index type, and $\eta : \kappa \to \Omega[F/\mathbb{C}]$ differentials with $Q.\mathrm{ordDifferential}(\eta_i) \geq 0$ at every place $Q$. For each cell $C$ let $V_C \subseteq \mathbb{C}$ be open with $(\mathcal{D}.\mathrm{cell}\,C).R.K \subseteq V_C \subseteq$ the chart target, and let $\Psi_{i,C}$ have derivative $\mathrm{coeffIn}\,\zeta_C\,\eta_i\,w$ at every $w \in V_C$. Assume the jumps are constant along edges: for each $i$ and edge $e$, on the whole parameter interval of the arc $\mathrm{arcOf}(e,\mathrm{true})$ the difference of $\Psi_{i}$ on the positive cell at the loop point and $\Psi_i$ on the negative cell at the chart image of the same boundary point equals $J_e(i)$. Let $\mathcal{T}, \mathcal{T}s$ be finite sets of edges with $J_e = 0$ for $e \in \mathcal{T}s$, and let $Z$ express every edge function valued in $\mathbb{Z}$, and every one valued in $\kappa \to \mathbb{C}$, that is Kirchhoff-closed (in-sum equals out-sum at each vertex) as $f_e = \sum_{j \in \mathcal{T}^c} Z_{j,e} \cdot f_j$. Assume finally that if some edge lies outside $\mathcal{T}s$ then there is a cyclic boundary word, i.e. $m$ with $\mathrm{NeZero}\,m$ and a bijection $wd : \mathbb{Z}/m \simeq \{(e,b) : e \notin \mathcal{T}s\}$ such that consecutive letters match end vertex to start vertex and their cells are joined by a list of cells chained by $\mathcal{T}s$-edges incident to that vertex, and such that the signed between-letter counting functions $pe_e$ (summing $\pm 1$ according to the orientation bit over the indices strictly between those of $(e,\mathrm{true})$ and $(e,\mathrm{false})$, restricted to letters with edge $e'$) are Kirchhoff-closed. The conclusion has three parts: first, the jump vectors are Kirchhoff-closed at every vertex; second, for every edge $f$ there are integers $n_l$ with $J_f = \sum_{l \in (\mathcal{T} \cup \mathcal{T}s)^c} n_l \cdot \bigl(i \mapsto \sum_e Z_{l,e}\,\mathcal{D}.\mathrm{edgeInt}(\eta_i)(e)\bigr)$; third, for every $m$, $wd$ satisfying the two word conditions and every $j \notin \mathcal{T}s$, $J_j = -\sum_{l \in (\mathcal{T} \cup \mathcal{T}s)^c} pe_{j,l} \cdot \bigl(i \mapsto \sum_e Z_{l,e}\,\mathcal{D}.\mathrm{edgeInt}(\eta_i)(e)\bigr)$.
--
--   This is the combinatorial heart of the bilinear-relations computation on the Riemann surface attached to a function field: the jumps between local primitives of regular differentials across the edges of a cell dissection obey a conservation law at the vertices, lie in the lattice spanned by the period vectors of the cycles indexed outside $\mathcal{T} \cup \mathcal{T}s$, and are computed explicitly by reading the cyclic boundary word of the dissection. It is used in the derivation of the loops/path-integral reciprocity statement [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw), and its proof cites the local calculus for `coeffIn` and the orientation-reversal identity for arc integrals of the boundary integrand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_jump_kirchhoff_and_wordFormula_of_primitives.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (𝒟 : CellDissection F) (hvert : Function.Injective 𝒟.vert) (κ : Type*) [Fintype κ]
    (η : κ → Ω[F⁄ℂ]) (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i))
    (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)
    (hΨ : ∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w)
    (J : 𝒟.ιE → κ → ℂ)
    (hJ : ∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i)
    (𝒯 𝒯s : Finset 𝒟.ιE) (hJ0 : ∀ e ∈ 𝒯s, J e = 0) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZ : ∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hZ' : ∀ f : 𝒟.ιE → κ → ℂ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hWD : (∃ e, e ∉ 𝒯s) → ∃ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
      let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
      let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
        ∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
              (i - wd.symm ⟨(e, true), he⟩).val <
                (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
          (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
          cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
              ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) :
    (∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e) ∧
    (∀ f : 𝒟.ιE, ∃ n : 𝒟.ιE → ℤ,
      J f = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (n l : ℂ) • ∑ e, (Z l e : ℂ) • fun i => 𝒟.edgeInt (η i) e) ∧
    ∀ (m : ℕ) (_ : NeZero m) (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}),
      let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
      let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
      let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
        ∑ i ∈ Finset.univ.filter
            (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
              (i - wd.symm ⟨(e, true), he⟩).val <
                (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
          (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
          cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
              ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) →
      (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) →
      ∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
        J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (pe j hj l : ℂ) • ∑ e, (Z l e : ℂ) • fun i => 𝒟.edgeInt (η i) e := by sorry
