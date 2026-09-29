-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
-- name    : CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/dc463384-9911-55b6-99f2-827c8958e052
-- title:
--   Inertia fixes every torus lift of an inertia-invariant point
-- statement:
--   Fix a finite type $E$, a type $V$ with decidable equality, a prime $r$, and a degeneracy datum $D$ on $(E,V)$ (two maps $a,b\colon E\to V$ and weights $w\colon E\to\mathbb{N}^{+}$), whose ribbon kernel $Z=$ `ribbonKernel D` is the intersection of the kernels of the two pushforwards $(E\to\mathbb{Z})\to(V\to\mathbb{Z})$ along $a$ and $b$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $r$ a nonunit of $A$, and assume the decomposition group of $A$ over $\mathbb{Q}$ acts isometrically, i.e. $A.\mathrm{valuation}(\sigma x)=A.\mathrm{valuation}(x)$ for all $\sigma$ in that group. Let $T$ be an abelian group, $S$ a group with homomorphisms $\mathrm{scalar}$ into the decomposition group, $\mathrm{actZ}$ into $\mathrm{Aut}_{\mathbb{Z}}(Z)$ and $\mathrm{gal}$ into $\mathrm{AddAut}(T)$, and let $\mathcal{U}$ be an equivariant uniformisation datum for these data: a subfield $K$ of the completion $\widehat{A}$ with a valuation-normalising $\mathrm{ord}$, Henselian $n$-th roots for $n$ prime to $r$ and inertia-invariance of $K$, a period datum $P$ over $(K,\widehat{A},\mathrm{ord})$ with symmetric $\mathbb{Z}$-bilinear $Q$ on $Z$ computing the ribbon Gram matrix, and a surjection $\mathrm{eFull}\colon P.\mathrm{TorusPoints}=\mathrm{Hom}_{\mathbb{Z}}(Z,\mathrm{Additive}\,\widehat{A}^{\times})\to T$ with kernel the period lattice, equivariant for $Q$ and for $\mathrm{coeffMap}$ composed with $\mathrm{precomp}$. Assume given a homomorphism $\iota$ from the decomposition group to $S$ splitting $\mathrm{scalar}$, such that $\mathrm{actZ}(\iota\tau)=1$ whenever the image of $\tau$ lies in the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ (the inertia subgroup pushed into $\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}}$). Let $u$ be a torus point with $\mathrm{gal}(\iota\tau)(\mathrm{eFull}\,u)=\mathrm{eFull}\,u$ for all such inertia $\tau$. Then for every such $\tau$ and every $\mathbb{Q}$-algebra automorphism $s$ of $\widehat{A}$ acting as $\tau$ on $\widehat{A}$, the coefficientwise action $P.\mathrm{coeffMap}(s)$ fixes $u$: postcomposing $u$ with $\mathrm{Units.map}\,s$ returns $u$.
--
--   In the Cerednik–Drinfeld/Mumford uniformisation part of the argument this is the "every lift" form of inertia-invariance: if a point of $T$ is fixed by inertia and inertia acts trivially on the ribbon (cycle) lattice, then each of its torus lifts is already inertia-invariant coefficientwise. It is used by [`CerednikDrinfeld.Mumford.EquivariantUniformization.exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq`](thm.html#CerednikDrinfeld.Mumford.EquivariantUniformization.exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq), which combines it with surjectivity of `eFull` to produce an invariant lift of a given invariant point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq.lean

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_mem_inertiaSubgroupIn_of_gal_eFull_eq
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    [Fact (A.DecompositionIsometric ℚ)]
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)
    (hι_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        actZ (ι τ) = 1)
    (u : 𝒰.P.TorusPoints)
    (hu : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        gal (ι τ) (𝒰.eFull u) = 𝒰.eFull u)
    (τ : ↥(A.decompositionSubgroup ℚ))
    (hτ : (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion) (hs : ∀ c, s c = τ • c) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by sorry
