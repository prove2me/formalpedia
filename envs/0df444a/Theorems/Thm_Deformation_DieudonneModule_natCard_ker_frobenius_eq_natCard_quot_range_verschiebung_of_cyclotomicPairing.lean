-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing
-- name    : Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/3cee3184-993d-5012-b887-9e3b9e9617ce
-- title:
--   Rank symmetry of F and V under a cyclotomic pairing
-- statement:
--   Let $p$ be an odd prime and let $\mathbb{Z}_{(p)}$ denote the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying a Hopf algebra structure over this ring which is finite and free as a module and whose comultiplication is cocommutative, and assume both that $H$ is a local ring and that its Cartier dual $\mathrm{CartierDual}$, namely the $\mathbb{Z}_{(p)}$-linear dual $\mathrm{Hom}(H,\mathbb{Z}_{(p)})$ with its induced ring structure, is a local ring. Let $\kappa$ be a finite field of characteristic $p$ and $N$ a finite-dimensional $\kappa$-vector space, and let $\rho$ be a monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` to the $\kappa$-linear endomorphisms of $N$. Assume given a bijection $e$ from the set of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$, equipped via `WithConv` with the convolution product, onto $N$ which turns convolution into addition, $e(f\ast g) = e(f)+e(g)$, and is Galois-equivariant in the sense that whenever $g$ is the pointwise composite of $f$ with $\sigma$ one has $e(g) = \rho(\sigma)(e(f))$. Assume further a $\kappa$-bilinear form $B$ on $N$ which is non-degenerate in the left variable (if $B(x,y)=0$ for all $y$ then $x=0$) and on which the Galois action is cyclotomic: for every $\sigma$ and every natural number $a$ such that $\sigma(\mu)=\mu^{a}$ for all $p$-th roots of unity $\mu$ in $\overline{\mathbb{Q}}$, one has $B(\rho(\sigma)x,\rho(\sigma)y) = a\,B(x,y)$ in $\kappa$. Form the base change $A = \mathbb{F}_p \otimes_{\mathbb{Z}_{(p)}} H$ and its Dieudonné module [`Deformation.DieudonneModule`](def/Dieudonne_WittHomColimit.html#L234), the direct limit over $n$ of the groups of primitive truncated Witt vectors of length $n$ with entries in $A$ — those $x$ with $(\Delta)_*x = (\iota_1)_*x + (\iota_2)_*x$ — along the shift maps, with the additive endomorphisms $F$ and $V$ induced by the Witt vector Frobenius and Verschiebung. The conclusion is that the kernel of $F$ and the quotient of the Dieudonné module by the image of $V$ have the same number of elements, as `Nat.card`.
--
--   This is the rank-symmetry statement $\#\ker F = \#\,\mathrm{coker}\,V$ on the Dieudonné module of the special fibre of a local–local finite flat group scheme whose $\overline{\mathbb{Q}}$-points carry a Galois-cyclotomic non-degenerate pairing, in the form used in Mazur's multiplicity-one argument; it is deliberately weaker than a full self-duality datum identifying $F$ with the transpose of $V$. It is used in the proof that the relevant Hecke torsion has rank at most two at $j = 0$, in [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct in

theorem Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_cyclotomicPairing
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H))
    {κ : Type} [Field κ] [Finite κ] [CharP κ p]
    {N : Type} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = ρ σ (e f))
    (B : N →ₗ[κ] N →ₗ[κ] κ) (hB : ∀ x : N, (∀ y : N, B x y = 0) → x = 0)
    (hBχ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
        ∀ x y : N, B (ρ σ x) (ρ σ y) = (a : κ) • B x y) :
    Nat.card (Deformation.DieudonneModule.frobenius (ZMod p) p
        ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)).ker =
      Nat.card (Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H) ⧸
        (Deformation.DieudonneModule.verschiebung (ZMod p) p
          ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)).range) := by sorry
