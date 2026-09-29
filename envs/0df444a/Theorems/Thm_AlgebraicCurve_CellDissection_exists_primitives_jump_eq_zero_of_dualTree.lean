-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree
-- name    : AlgebraicCurve.CellDissection.exists_primitives_jump_eq_zero_of_dualTree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/32bd4d87-9563-5fe9-930c-8ceb7bdbe4e8
-- title:
--   Normalised cell primitives of regular differentials on a dual tree
-- statement:
--   Let $F$ be a field of characteristic-zero type over $\mathbb{C}$ that is a curve over $\mathbb{C}$ in the sense of `IsCurveOver` (principal divisors, each place having residue field finite over $\mathbb{C}$, and $\Omega[F\!\mid\!\mathbb{C}]$ free of rank one over $F$) and essentially of finite type, with the place space $\mathrm{Place}\,\mathbb{C}\,F$ carrying a Hausdorff charted structure making it an analytic manifold over the model $\mathbb{C}$. Assume: some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x)$; and for every $f \neq 0$ and every place $v$, the chart-read function $z \mapsto \mathrm{evalAt}$ of $f$ at the point with extended chart coordinate $z$ is meromorphic at the coordinate of $v$ with `meromorphicOrderAt` equal to $v.\mathrm{ord}\,f$. Let $\mathcal{D}$ be a cell dissection of $F$ (finite families of cells, edges and vertices, each cell a radial region in an analytic chart, with the side map pairing cell arcs bijectively with oriented edges), $\kappa$ a type, and $\eta : \kappa \to \Omega[F\!\mid\!\mathbb{C}]$ a family with $0 \le Q.\mathrm{ordDifferential}(\eta_i)$, i.e. $\mathrm{ord}_Q$ of the differential coefficient of $\eta_i$ is non-negative, at every place $Q$. Let $\mathcal{T}s$ be a finite set of edges such that for all cells $C, C'$ there is exactly one $c : \mathcal{D}.\iota E \to \mathbb{Z}$ vanishing off $\mathcal{T}s$ whose boundary, namely for each cell $D$ the sum of $c\,e$ over edges whose positive side lies in $D$ minus the sum over edges whose negative side lies in $D$, equals $\mathbf{1}_{D = C'} - \mathbf{1}_{D = C}$. Finally let $C_0$ be a cell and $w_0 \in \mathbb{C}$. Then there are $V : \mathcal{D}.\iota C \to \mathrm{Set}\,\mathbb{C}$, $\Psi : \kappa \to \mathcal{D}.\iota C \to \mathbb{C} \to \mathbb{C}$ and $J : \mathcal{D}.\iota E \to \kappa \to \mathbb{C}$ such that each $V\,C$ is open, contains the closed radial region $K$ of the cell $C$, lies in the target of its chart $\zeta$, and is star-convex with respect to the centre $q$ of that radial region; for all $i$ and $C$ and all $w \in V\,C$, $\Psi_i\,C$ has derivative $\mathrm{coeffIn}\,\zeta_C\,(\eta_i)\,w$ at $w$; for each $i$ and each edge $e$, with $(C^{+},k^{+})$ and $(C^{-},k^{-})$ the cell-arc pairs assigned to $e$ with its two orientations, the difference of $\Psi_i\,C^{+}$ at the boundary loop point of $C^{+}$ at parameter $s$ and of $\Psi_i\,C^{-}$ at the $\zeta_{C^{-}}$-coordinate of that same boundary point is equal to $J\,e\,i$ for every $s$ in the closed parameter interval of the arc $k^{+}$; $J\,e = 0$ for every $e \in \mathcal{T}s$; and $\Psi_i\,C_0\,w_0 = 0$ for all $i$.
--
--   This is the construction of cell-by-cell primitives of a family of regular differentials on the Riemann surface of a complex function field, with the additive constants fixed so that the jump of each primitive across an edge is constant along that edge and vanishes on the chosen edge set $\mathcal{T}s$, a spanning tree of the dual graph. It feeds the reciprocity statement for path integrals along loops, [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_exists_primitives_jump_eq_zero_of_dualTree.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.exists_primitives_jump_eq_zero_of_dualTree
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
    (𝒟 : CellDissection F) (κ : Type*) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i (Q : Place ℂ F), 0 ≤ Q.ordDifferential (η i)) (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
      ∀ D, (∑ e with (𝒟.arcOf (e, true)).1 = D, c e) -
          (∑ e with (𝒟.arcOf (e, false)).1 = D, c e) =
        (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (C₀ : 𝒟.ιC) (w₀ : ℂ) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (J : 𝒟.ιE → κ → ℂ),
      (∀ C, IsOpen (V C)) ∧ (∀ C, (𝒟.cell C).R.K ⊆ V C) ∧ (∀ C, V C ⊆ (𝒟.cell C).ζ.target) ∧
      (∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)) ∧
      (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C) (coeffIn (𝒟.cell C).ζ (η i) w) w) ∧
      (∀ i (e : 𝒟.ιE),
      ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ i (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ i (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e i) ∧
      (∀ e ∈ 𝒯s, J e = 0) ∧ ∀ i, Ψ i C₀ w₀ = 0 := by sorry
