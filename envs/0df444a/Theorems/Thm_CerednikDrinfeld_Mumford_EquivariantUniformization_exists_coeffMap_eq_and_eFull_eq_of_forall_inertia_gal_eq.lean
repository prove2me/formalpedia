-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
-- name    : CerednikDrinfeld.Mumford.EquivariantUniformization.exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/03eebac2-b1db-55cc-af5e-7bef1a390b9d
-- title:
--   Inertia-invariant points lift to inertia-invariant torus points
-- statement:
--   Fix finite data: types $E$, $V$ with $E$ finite and $V$ with decidable equality, a prime $r$, and a degeneracy datum $D$ on $(E,V)$ (maps $a,b \colon E \to V$ and weights $w \colon E \to \mathbb{N}^{+}$), whose ribbon lattice $\mathrm{ribbonKernel}\ D \subseteq (E \to \mathbb{Z})$ is the intersection of the kernels of the two pushforwards along $a$ and $b$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $r$ a nonunit of $A$, whose decomposition subgroup over $\mathbb{Q}$ acts isometrically for $A$'s valuation. Let $T$ be an additive commutative group, $S$ a group equipped with homomorphisms $scalar$ to the decomposition subgroup, $actZ$ to the group of $\mathbb{Z}$-linear automorphisms of $\mathrm{ribbonKernel}\ D$, and $gal$ to $\mathrm{AddAut}\ T$, and let $\mathcal{U}$ be an `EquivariantUniformization` for these data: an intermediate field $K$ between $\mathbb{Q}$ and the completion $\hat{\mathbb{Q}}_A$ of $A$'s valuation, an order homomorphism $ord$ on $\mathrm{Additive}\ K^{\times}$ computing valuations as powers of $v(r)$, pointwise fixity of $K$ under automorphisms of $\hat{\mathbb{Q}}_A$ induced by inertia, a Hensel-type $n$-th root property for units of order $0$ with $n$ positive and prime to $r$, a period datum $P$ over $D$ with respect to $K$, $\hat{\mathbb{Q}}_A$ and $ord$, and an additive surjection $\mathcal{U}.eFull$ from $P.TorusPoints = \mathrm{Hom}_{\mathbb{Z}}(\mathrm{ribbonKernel}\ D, \mathrm{Additive}\ \hat{\mathbb{Q}}_A^{\times})$ onto $T$ with kernel the period lattice, together with the $S$-equivariance of the period form $Q$ and of $\mathcal{U}.eFull$. Assume further a homomorphism $\iota$ from the decomposition subgroup to $S$ splitting $scalar$ (so $scalar(\iota\tau) = \tau$ for all $\tau$), such that $actZ(\iota\tau) = 1$ whenever the underlying automorphism of $\tau$ lies in the inertia subgroup of $A$ inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, and let $z \in T$ satisfy $gal(\iota\tau)\,z = z$ for all such inertia $\tau$. Then there exists a torus point $u \in P.TorusPoints$ with $\mathcal{U}.eFull\,u = z$ which is invariant coefficientwise under inertia: for every $\tau$ in the decomposition subgroup whose underlying automorphism lies in the inertia subgroup and every $\mathbb{Q}$-algebra automorphism $s$ of $\hat{\mathbb{Q}}_A$ with $s\,c = \tau \cdot c$ for all $c$, one has $P.coeffMap\ s\ u = u$, i.e. $u$ followed by the automorphism of $\mathrm{Additive}\ \hat{\mathbb{Q}}_A^{\times}$ induced by $s$ equals $u$.
--
--   This is the invariance clause of the equivariant Mumford–Raynaud uniformisation package: inertia-fixed points of the abstract group $T$ are realised by torus points that are themselves fixed, coordinatewise, by inertia acting through automorphisms of the completion. It is used in establishing the existence of an equivariant uniformisation for the degree-zero Picard group of a Čerednik–Drinfeld Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_EquivariantUniformization_exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq.lean

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.EquivariantUniformization.exists_coeffMap_eq_and_eFull_eq_of_forall_inertia_gal_eq
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
    (z : T)
    (hz : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        gal (ι τ) z = z) :
    ∃ u : 𝒰.P.TorusPoints,
      (∀ τ : ↥(A.decompositionSubgroup ℚ),
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = τ • c) →
          𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u) ∧
      𝒰.eFull u = z := by sorry
