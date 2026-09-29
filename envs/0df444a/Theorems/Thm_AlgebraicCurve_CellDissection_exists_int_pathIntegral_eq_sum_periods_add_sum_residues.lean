-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues
-- name    : AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/abac4d98-202b-5fbe-a7b3-44842aa32253
-- title:
--   Periods of third-kind differentials along loops avoiding poles
-- statement:
--   Let $F$ be a field over $\mathbb{C}$ which is a curve over $\mathbb{C}$ (principal divisors, finite residue extensions, and $\Omega[F\!\mid\!\mathbb{C}]$ free of rank one) and essentially of finite type, with $\mathrm{Place}\,\mathbb{C}\,F$ a Hausdorff analytic $\mathbb{C}$-manifold; assume $F$ contains a transcendental $x$ with $F$ finite over $\mathbb{C}(x)$, and that each nonzero $f \in F$ reads, in the chart at any place $v$, as a meromorphic function whose order at the chart centre is $v.\mathrm{ord}\,f$; assume the regular differentials are finite-dimensional over $\mathbb{C}$. Let $\mathcal{D}$ be a cell dissection with injective vertex map, and $S$ a finite set of places meeting each closed cell in at most one point, each $v \in S$ lying in some open cell's interior at its radial centre $R.q$. Let $\mathcal{T}, \mathcal{T}s$ be finsets of edges such that for all cells $C, C'$ there is a unique integer edge function supported in $\mathcal{T}s$ with dual boundary $[C'] - [C]$; let $Z$ express every Kirchhoff-closed edge function (equal in- and out-sums at each vertex), with values in $\mathbb{Z}$ or in any abelian group, as $f(e) = \sum_{j \notin \mathcal{T}} Z\,j\,e \cdot f(j)$; let $\gamma\,l$ be loops at $\mathcal{D}.\mathrm{vert}(\mathcal{D}.\mathrm{ends}\,l).1$ which for $l \notin \mathcal{T}$ lie in the skeleton and satisfy, for every differential nonnegative along the skeleton, existence of a primitive along $\gamma\,l$ and $\int_{\gamma l}\theta = \sum_e Z\,l\,e\cdot\mathcal{D}.\mathrm{edgeInt}\,\theta\,e$. Assume further, whenever some edge lies outside $\mathcal{T}s$, a cyclic enumeration $wd$ of $\mathbb{Z}/m$ by the oriented arcs of edges outside $\mathcal{T}s$ whose consecutive letters share a vertex and whose cells are joined by a chain of $\mathcal{T}s$-edges incident there, and whose letter-interval counting functions $pe$ are Kirchhoff-closed. Then for every loop $\delta$ at a place $Pt$ avoiding $S$ there exist integers $c\,l$ and $w\,v$, independent of the differential, such that for all $\vartheta \in \Omega[F\!\mid\!\mathbb{C}]$ with $v.\mathrm{ordDifferential}\,\vartheta \ge -1$ everywhere and $\ge 0$ off $S$, $$\int_\delta \vartheta = \sum_{l \notin \mathcal{T} \cup \mathcal{T}s} c\,l \int_{\gamma l}\vartheta + 2\pi i \sum_{v \in S} w\,v \cdot \mathrm{evalAt}_v\big(v.\mathrm{dCoordFn}\cdot v.\mathrm{differentialCoeff}\,\vartheta\big),$$ the last factor being the residue of $\vartheta$ at $v$.
--
--   This is the period decomposition for differentials of the third kind: a loop integral of a differential with at worst simple poles, all inside $S$, splits into an integral combination of the periods over the cycle loops $\gamma\,l$ plus $2\pi i$ times an integral combination of residues, with coefficients depending only on the loop and the dissection. It feeds the reciprocity statement [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues
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
    [Module.Finite ℂ ↥(regularDifferentials ℂ F)]
    (𝒟 : CellDissection F) (hvert : Function.Injective 𝒟.vert) (S : Finset (Place ℂ F))
    (hS2 : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hS5 : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧ (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (𝒯 𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (𝒟.arcOf (e, true)).1 = D, c e) -
          (∑ e with (𝒟.arcOf (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hZ : ∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (hZall : ∀ (A : Type) [AddCommGroup A], ∀ f : 𝒟.ιE → A,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j)
    (γ : ∀ l : 𝒟.ιE, Path (𝒟.vert (𝒟.ends l).1) (𝒟.vert (𝒟.ends l).1))
    (hγs : ∀ l ∉ 𝒯, ∀ t, γ l t ∈ 𝒟.skeleton)
    (hγi : ∀ l ∉ 𝒯, ∀ θ : Ω[F⁄ℂ], (∀ x ∈ 𝒟.skeleton, 0 ≤ x.ordDifferential θ) →
      (∃ g, IsPrimitiveAlong θ (γ l) g) ∧ pathIntegral θ (γ l) = ∑ e, (Z l e : ℂ) * 𝒟.edgeInt θ e)
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
        (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f)
    {Pt : Place ℂ F} (δ : Path Pt Pt) (hδ : ∀ t, δ t ∉ S) :
    ∃ (c : 𝒟.ιE → ℤ) (w : Place ℂ F → ℤ), ∀ ϑ : Ω[F⁄ℂ],
      (∀ v : Place ℂ F, -1 ≤ v.ordDifferential ϑ) →
      (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential ϑ) →
      pathIntegral ϑ δ = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, (c l : ℂ) * pathIntegral ϑ (γ l) +
        2 * π * I * ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff ϑ) := by sorry
