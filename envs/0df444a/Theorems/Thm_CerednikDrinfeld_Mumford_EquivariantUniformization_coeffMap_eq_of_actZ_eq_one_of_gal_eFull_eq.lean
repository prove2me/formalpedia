-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
-- name    : CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/933b27e2-dba6-52f7-a7d3-f37a37ab2182
-- title:
--   Coefficientwise invariance of torus points with invariant image
-- statement:
--   Fix a finite type $E$, a type $V$ with decidable equality, a prime $r$, and a degeneracy datum $D$ on $E$, $V$ (maps $a,b : E \to V$ and weights $w : E \to \mathbb{N}_{>0}$), whose ribbon kernel $Z = \mathrm{ribbonKernel}\,D$ is the intersection of the kernels of the two pushforward maps $(E \to \mathbb{Z}) \to (V \to \mathbb{Z})$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $r$ a non-unit of $A$ (the hypothesis `hA : A.LiesOverPrime r`), an additive group $T$, a group $S$, and homomorphisms $\mathrm{scalar}$ from $S$ to the decomposition subgroup of $A$ over $\mathbb{Q}$, $\mathrm{actZ}$ from $S$ to $\mathbb{Z}$-linear automorphisms of $Z$, and $\mathrm{gal}$ from $S$ to additive automorphisms of $T$. Let $\mathcal{U}$ be an equivariant uniformisation for these data, so in particular it provides an intermediate field $K$ of $\mathbb{Q}$ in the completion $L$ of $A.\mathrm{valuation}$, an order homomorphism on $K^\times$, a period datum $P$ over $D$ with symmetric form $Q$ on $Z$ valued in $\mathrm{Additive}\,K^\times$ satisfying $\mathrm{ord}\,Q(x,y) = \mathrm{ribbonGram}\,D\,x\,y$, and a surjective homomorphism $\mathrm{eFull}$ from the torus points $P.\mathrm{TorusPoints} = \mathrm{Hom}_{\mathbb{Z}}(Z, \mathrm{Additive}\,L^\times)$ onto $T$ whose kernel is exactly the period lattice, together with the equivariance of $Q$ and of $\mathrm{eFull}$. Let $\sigma \in S$ satisfy $\mathrm{actZ}\,\sigma = 1$, let $s$ be a $\mathbb{Q}$-algebra automorphism of $L$ with $s(c) = \mathrm{scalar}(\sigma) \cdot c$ for all $c$ and with $v(s(c)) = v(c)$ for all $c$, and let $u$ be a torus point with $\mathrm{gal}\,\sigma(\mathrm{eFull}\,u) = \mathrm{eFull}\,u$. Then applying $s$ to the coefficients of $u$, i.e. $P.\mathrm{coeffMap}$ of the underlying ring homomorphism of $s$ evaluated at $u$, returns $u$ itself.
--
--   This is the rigidity step in the equivariant Mumford uniformisation of a degenerating abelian variety attached to a degeneracy datum: a torus point whose image in the uniformised group is fixed by a symmetry acting trivially on the cycle lattice is fixed coefficientwise. It is used to derive the corresponding statement for elements of the inertia subgroup, in [`CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq`](thm.html#CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq.lean

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (σ : S) (hσ : actZ σ = 1)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion)
    (hs : ∀ c, s c = (scalar σ) • c)
    (hiso : ∀ c, Valued.v (s c) = Valued.v c)
    (u : 𝒰.P.TorusPoints) (hu : gal σ (𝒰.eFull u) = 𝒰.eFull u) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by sorry
