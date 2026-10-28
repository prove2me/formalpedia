-- Prove2me | Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
-- name    : FiniteEnergyPlane.rescale_isFiniteEnergyCurve
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T17:56:18.493621+00:00
-- url     : https://prove2.me/theorems/1c58cbae-578b-48a5-8cd5-27600560c007
-- title:
--   Domain rescaling and R-translation of finite-energy curves in a symplectization
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, with associated almost complex structure $\tilde J$ on $\mathbb R^{2n+2}\setminus\{0\}\cong\mathbb R\times S$. Let $U\subseteq\mathbb C$ be open and $u$ a finite-energy $\tilde J$-holomorphic curve on $U$. Let $z_0\in\mathbb C$, $s>0$, $c>0$, and put
--   $$v(w)=c\,u(z_0+s\,w),\qquad W=\{w\in\mathbb C: z_0+s\,w\in U\}.$$
--   Then:
--   1. $v$ is a finite-energy $\tilde J$-holomorphic curve on $W$;
--   2. $a(v(w))=a(u(z_0+sw))+\tfrac12\log c$ for $w\in W$, where $a$ is the $\mathbb R$-coordinate;
--   3. $|\nabla v(w)|=s\,|\nabla u(z_0+sw)|$ for $w\in W$, in the $\mathbb R$-invariant gradient norm;
--   4. for every measurable $A\subseteq U$, the Hofer energy and the $d\lambda$-energy of $v$ on $\{w: z_0+sw\in A\}$ equal the Hofer energy and the $d\lambda$-energy of $u$ on $A$.
--
--   These are the invariances of finite-energy curves under affine rescaling of the domain and translation in the $\mathbb R$-direction of the symplectization.
--
--   **Formalization Note** The translation by $\tfrac12\log c$ in the coordinate $a$ (where $y=e^{2a}x$, $x\in S$) is multiplication by $c$ in $\mathbb R^{2n+2}$. $|\nabla u|$ is `gradNorm H u` $=\|D(a\circ u)\|+\|D(\mathrm{proj}\circ u)\|$; the energies are `energy` and `dlambdaEnergy` from the setting.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, proof of Lemma 2.20, p. 12; H. Hofer, Invent. Math. 114 (1993), Section 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Rescaling a finite-energy curve in the domain and translating it in the `ℝ`-direction. Let
`u` be a finite-energy `J̃`-holomorphic curve on an open `U ⊆ ℂ`, `z₀ ∈ ℂ`, `s > 0` and `c > 0`,
and put `v(w) = c • u(z₀ + s w)` on `W = {w | z₀ + s w ∈ U}`. Then `v` is a finite-energy
`J̃`-holomorphic curve on `W`, `a(v(w)) = a(u(z₀ + s w)) + (log c)/2`,
`|∇v(w)| = s |∇u(z₀ + s w)|` in the `ℝ`-invariant norm `gradNorm`, and for every measurable
`A ⊆ U` the Hofer energy and the `dλ`-energy of `v` on `{w | z₀ + s w ∈ A}` equal those of `u`
on `A`. -/
theorem rescale_isFiniteEnergyCurve {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (z₀ : ℂ) (s : ℝ) (hs : 0 < s) (c : ℝ)
    (hc : 0 < c) :
    IsFiniteEnergyCurve H J {w | z₀ + s • w ∈ U} (fun w => c • u (z₀ + s • w)) ∧
      (∀ w, z₀ + s • w ∈ U →
        aCoord H (c • u (z₀ + s • w)) = aCoord H (u (z₀ + s • w)) + Real.log c / 2) ∧
      (∀ w, z₀ + s • w ∈ U →
        gradNorm H (fun w => c • u (z₀ + s • w)) w = s * gradNorm H u (z₀ + s • w)) ∧
      ∀ A ⊆ U, MeasurableSet A →
        energy H {w | z₀ + s • w ∈ A} (fun w => c • u (z₀ + s • w)) = energy H A u ∧
          dlambdaEnergy H {w | z₀ + s • w ∈ A} (fun w => c • u (z₀ + s • w)) =
            dlambdaEnergy H A u := by
  sorry

end FiniteEnergyPlane
