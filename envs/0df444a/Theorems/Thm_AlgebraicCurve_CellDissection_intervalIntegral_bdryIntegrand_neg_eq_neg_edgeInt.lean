-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
-- name    : AlgebraicCurve.CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/9b3ca0b0-eccb-5b8e-ab60-08fe63e875a5
-- title:
--   Reversed copy of an edge integrates to minus the edge integral
-- statement:
--   Let $F$ be a field with a $\mathbb{C}$-algebra structure which is a curve over $\mathbb{C}$ (principal divisors, residue fields finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ free of rank one) and essentially of finite type over $\mathbb{C}$, and suppose the place space $\mathrm{Place}\,\mathbb{C}\,F$ carries a Hausdorff topology and a $\mathbb{C}$-charted space structure making it an analytic manifold on the model $\mathcal{I}(\mathbb{C},\mathbb{C})$. Assume $hfg$: some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite-dimensional over $\mathbb{C}(x)$; and $hF$: for every $f \neq 0$ in $F$ and every place $v$, the function $z \mapsto \mathrm{evalAt}$ of $f$ at the point with extended chart coordinate $z$ is meromorphic at the chart image of $v$, with meromorphic order there equal to $v.\mathrm{ord}\,f$. Let $\mathcal{D}$ be a cell dissection of $F$, let $\theta \in \Omega[F/\mathbb{C}]$, and let $e$ be an edge index. Write $(C^{+},k^{+}) = \mathcal{D}.\mathrm{arcOf}(e,\mathrm{true})$ and $(C^{-},k^{-}) = \mathcal{D}.\mathrm{arcOf}(e,\mathrm{false})$ for the unique cell-and-side pairs whose side label is $(e,\mathrm{true})$, resp. $(e,\mathrm{false})$. Assume that for every parameter $s$ in the closed interval $[\varphi_{k^{+}},\varphi_{k^{+}+1}]$ of the positive arc, the boundary point $\mathcal{D}.\mathrm{cell}\,C^{+}.\mathrm{bdry}\,s$ has $\mathrm{ordDifferential}\,\theta \geq 0$, i.e. $\theta$ has non-negative order along that arc. Then the interval integral of the boundary integrand $\mathrm{coeffIn}\,\zeta\,\theta(R.\mathrm{loop}\,t)\cdot R.\mathrm{loop}'\,t$ of the cell $C^{-}$ over the parameter interval $[\varphi_{k^{-}},\varphi_{k^{-}+1}]$ equals $-\mathcal{D}.\mathrm{edgeInt}\,\theta\,e$, the latter being the same integrand for $C^{+}$ integrated over the positive arc.
--
--   This is the cancellation lemma for the two boundary copies of an edge in a cell dissection: the negatively labelled arc is an orientation-reversing reparametrisation of the positively labelled one, so the two contributions to a sum over cell boundaries are opposite. It is used in the assembly of boundary sums into periods and residues, by [`AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues`](thm.html#AlgebraicCurve.CellDissection.exists_int_pathIntegral_eq_sum_periods_add_sum_residues), [`AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives`](thm.html#AlgebraicCurve.CellDissection.jump_kirchhoff_and_wordFormula_of_primitives) and [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.intervalIntegral_bdryIntegrand_neg_eq_neg_edgeInt
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
    (𝒟 : CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE)
    (hθ : ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
        ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
      0 ≤ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s).ordDifferential θ) :
    ∫ t in ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.castSucc)..
        ((𝒟.cell (𝒟.arcOf (e, false)).1).R.φs (𝒟.arcOf (e, false)).2.succ),
      (𝒟.cell (𝒟.arcOf (e, false)).1).bdryIntegrand θ t = -𝒟.edgeInt θ e := by sorry
