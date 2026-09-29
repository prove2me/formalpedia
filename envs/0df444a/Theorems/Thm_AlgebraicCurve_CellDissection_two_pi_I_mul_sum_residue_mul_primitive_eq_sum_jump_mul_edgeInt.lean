-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
-- name    : AlgebraicCurve.CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/67b765ef-01b1-500a-ba61-3b672f21812a
-- title:
--   Summed residue theorem over a cell dissection
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure which is a curve over $\mathbb{C}$ (principal divisors, residue fields finite over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ free of rank one over $F$), essentially of finite type over $\mathbb{C}$, whose place space $\mathrm{Place}\,\mathbb{C}\,F$ carries a Hausdorff topology and a $\mathbb{C}$-analytic one-dimensional manifold structure. Assume `hfg`: some $x \in F$ is transcendental over $\mathbb{C}$ with $F$ finite over $\mathbb{C}(x)$; and `hF`: for every $f \neq 0$ and every place $v$, the function $z \mapsto \mathrm{evalAt}_{(\mathrm{extChartAt})^{-1}(z)}(f)$ is meromorphic at the chart image of $v$ with meromorphic order there equal to $v.\mathrm{ord}\,f$. Let $\mathcal{D}$ be a cell dissection: finite index types of cells, edges and vertices, cells given by a radial region (centre, positive continuous $2\pi$-periodic radius, angular subdivision $\varphi_s$ with $C^2$ radius on each arc) together with a chart $\zeta$, side data identifying each cell arc with an oriented edge bijectively, compatible arc endpoints and orientation-reversing reparametrisations, covering and connectivity. Let `poles` be a finite set of places, $c$ an assignment of a cell to each place with every $v \in$ `poles` lying in the open cell $\zeta_{c\,v}^{-1}(\{z : \|z-q\| < r(\arg(z-q))\})$. Let $\theta \in \Omega[F/\mathbb{C}]$ satisfy $v.\mathrm{ordDifferential}\,\theta \geq -1$ at the places of `poles` and $\geq 0$ elsewhere, where $\mathrm{ordDifferential}$ is the order of the coefficient of $\theta$ against $v.\mathrm{dCoord}$. Let $\eta \in \Omega[F/\mathbb{C}]$, and for each cell $C$ let $V\,C \subseteq \mathbb{C}$ be open with $(\mathcal{D}.\mathrm{cell}\,C).R.K \subseteq V\,C \subseteq \zeta_C$'s target, and $\Psi\,C : \mathbb{C} \to \mathbb{C}$ a primitive on $V\,C$ of the local coefficient $\mathrm{coeffIn}\,\zeta_C\,\eta$. Then there is $J : \mathcal{D}.\iota E \to \mathbb{C}$ such that for every edge $e$, writing $(C,k) = \mathcal{D}.\mathrm{arcOf}(e,\mathrm{true})$ and $(C',k') = \mathcal{D}.\mathrm{arcOf}(e,\mathrm{false})$, for all $s$ in $[\varphi_s(k.\mathrm{castSucc}), \varphi_s(k.\mathrm{succ})]$ the difference $\Psi\,C(R_C.\mathrm{loop}\,s) - \Psi\,C'(\zeta_{C'}(\mathrm{bdry}_C\,s))$ equals $J\,e$, and $$2\pi i \sum_{v \in \text{poles}} \mathrm{evalAt}_v\big(v.\mathrm{dCoordFn}\cdot v.\mathrm{differentialCoeff}\,\theta\big)\,\Psi\,(c\,v)\big(\zeta_{c\,v}(v)\big) = \sum_{e} J\,e \cdot \mathcal{D}.\mathrm{edgeInt}\,\theta\,e,$$ the edge integral being the integral of the boundary integrand of $\theta$ along the positively oriented arc of $e$ over its parameter interval.
--
--   This is the residue theorem applied cell by cell to the differential $\theta$ weighted by local primitives of $\eta$, with the boundary contributions regrouped edge by edge; the constancy of the jump of the primitives across each edge is what makes the regrouping possible. It is the analytic input to [`AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw`](thm.html#AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw), the reciprocity law between periods and residues on the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt.lean

import Definitions.Def_AlgebraicCurve_CellDissection
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.CellDissection.two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt
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
    (𝒟 : CellDissection F) (poles : Finset (Place ℂ F)) (c : Place ℂ F → 𝒟.ιC)
    (hc : ∀ v ∈ poles, v ∈ (𝒟.cell (c v)).interior')
    (θ : Ω[F⁄ℂ]) (hθpol : ∀ v ∈ poles, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q : Place ℂ F, Q ∉ poles → 0 ≤ Q.ordDifferential θ)
    (η : Ω[F⁄ℂ]) (V : 𝒟.ιC → Set ℂ) (hV : ∀ C, IsOpen (V C)) (hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C)
    (hVt : ∀ C, V C ⊆ (𝒟.cell C).ζ.target)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (hΨ : ∀ C, ∀ w ∈ V C, HasDerivAt (Ψ C) (coeffIn (𝒟.cell C).ζ η w) w) :
    ∃ J : 𝒟.ιE → ℂ,
      (∀ e : 𝒟.ιE, ∀ s ∈ Icc ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)
          ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
        Ψ (𝒟.arcOf (e, true)).1 ((𝒟.cell (𝒟.arcOf (e, true)).1).R.loop s) -
          Ψ (𝒟.arcOf (e, false)).1
            ((𝒟.cell (𝒟.arcOf (e, false)).1).ζ ((𝒟.cell (𝒟.arcOf (e, true)).1).bdry s)) = J e) ∧
      2 * π * I * ∑ v ∈ poles,
          Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) * Ψ (c v) ((𝒟.cell (c v)).ζ v) =
        ∑ e : 𝒟.ιE, J e * 𝒟.edgeInt θ e := by sorry
