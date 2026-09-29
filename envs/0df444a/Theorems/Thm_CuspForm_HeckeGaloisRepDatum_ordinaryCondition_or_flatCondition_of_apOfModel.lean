-- Prove2me | Theorems.Thm_CuspForm_HeckeGaloisRepDatum_ordinaryCondition_or_flatCondition_of_apOfModel
-- name    : CuspForm.HeckeGaloisRepDatum.ordinaryCondition_or_flatCondition_of_apOfModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/8f979908-4821-57f6-bfa5-505813573b03
-- title:
--   Ordinary or flat deformation condition at p for a Hecke–Galois datum
-- statement:
--   Fix a prime $p$ (as a `Fact`) with $p \neq 2$, and a Weierstrass model $W$ over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is semistable in the project's sense `IsSemistableModel`, i.e. no prime dividing $\Delta_W$ divides $c_4(W)$. Assume the $p$-torsion subgroup of the points of the base change of $W$ to an algebraic closure of $\mathbb{Q}$ has exactly $p^2$ elements, and that the induced action `galoisRepModuleEnd` on it factors through a finite level, i.e. is trivial on all automorphisms fixing some finite-dimensional intermediate field; these two hypotheses produce the residual representation `residualGaloisRepOf` over $\mathbb{Z}/p$. Let $S$ be a finite set of primes containing $p$ and all primes dividing $\Delta_W$; let $\mathcal{O}$ be a complete discrete valuation ring of characteristic $0$ with finite residue field and with $p$ in its maximal ideal, and $\iota : \mathbb{Z}/p \to k_{\mathcal{O}}$ a ring homomorphism such that the base change of the residual representation along $\iota$ is absolutely irreducible (irreducible after base change to an algebraic closure). Let $N \neq 0$ have all its prime factors in $S$, satisfy $q^2 \mid N$ for every $q \in S$ with $q \neq p$, satisfy $p \mid N$ and $p^2 \nmid N$ whenever $p \mid \Delta_W$ or $p \nmid a_p(W)$, and satisfy $p \nmid N$ whenever $p \nmid \Delta_W$ and $p \mid a_p(W)$; here $a_\ell(W)$ is `apOfModel`, the trace of Frobenius of the reduction. Let $\theta$ be a ring homomorphism from the Hecke algebra `heckeAlgebra N 2 S` to $k_{\mathcal{O}}$ sending $T_\ell$ to the residue of $a_\ell(W)$ for all primes $\ell \notin S$ with $\ell \nmid N$, let $T$ be a complete local Noetherian $\mathcal{O}$-algebra, finite and free as an $\mathcal{O}$-module with local structure map, and let $H$ be a [`CuspForm.HeckeGaloisRepDatum`](def/CuspForm_HeckeGaloisRepDatum.html#L8) for these data, with attached representation $H.\rho$ over $T$. The conclusion is the conjunction of two implications: if $p \mid \Delta_W$ or $p \nmid a_p(W)$ then $H.\rho$ satisfies [`GaloisRep.ordinaryCondition 𝒪 p S`](def/GaloisRep_LocalConditions.html#L28), i.e. its determinant is cyclotomic in the sense of `DetIsCyclotomic`, it is ordinary at $p$ (`IsOrdinaryAt`: a line spanned by a basis vector, stable under each decomposition group at $p$, with inertia acting trivially modulo it) and unramified at every prime outside $S$; and if $p \nmid \Delta_W$ and $p \mid a_p(W)$ then $H.\rho$ satisfies [`GaloisRep.flatCondition 𝒪 p S`](def/GaloisRep_Flat.html#L47), the same two outer conditions with ordinarity replaced by the project's finite-flatness `IsFlatAt p` at each finite level.
--
--   Classically this is the local–global compatibility at $p$ of the Galois representation carried by a Hecke algebra: ordinarity at $p$ for representations attached to $p$-ordinary Hecke eigensystems, and finite flatness at $p$ for level prime to $p$, together with the cyclotomic determinant and unramifiedness outside the level. The formal statement differs from the textbook version in that the representation is not constructed here: it is the $\rho$ field of a `HeckeGaloisRepDatum`, whose defining properties (characteristic polynomial of Frobenius at $\ell \nmid N$, $\ell \notin S$, residual absolute irreducibility, the $\theta$-compatibility and the universal point property) are taken as given, and the elliptic curve enters only through $\Delta_W$ and the traces $a_\ell(W)$, which select the case and pin down $\theta$. It is used as the deformation-type input in the modularity lifting theorems `modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd` and `modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd` for semistable curves at $p = 3, 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_HeckeGaloisRepDatum_ordinaryCondition_or_flatCondition_of_apOfModel.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_Algebra_PatchingDatum
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem CuspForm.HeckeGaloisRepDatum.ordinaryCondition_or_flatCondition_of_apOfModel (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (ι : ZMod p →+* IsLocalRing.ResidueField 𝒪)
    (habs : (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).baseChangeAlong
      ι).IsAbsolutelyIrreducible)
    {N : ℕ} [NeZero N]
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNS2 : ∀ q ∈ S, q ≠ p → q ^ 2 ∣ N)
    (hNp_ord : (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → p ∣ N ∧ ¬ p ^ 2 ∣ N)
    (hNp_flat : W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → ¬ p ∣ N)
    {θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪}
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = IsLocalRing.residue 𝒪 ((W.apOfModel ℓ : ℤ) : 𝒪))
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N (↑S : Set ℕ) 𝒪 θ T) :
    ((¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p) → GaloisRep.ordinaryCondition 𝒪 p S H.ρ) ∧
    (W.IsGoodPrimeFor p → (p : ℤ) ∣ W.apOfModel p → GaloisRep.flatCondition 𝒪 p S H.ρ) := by sorry
