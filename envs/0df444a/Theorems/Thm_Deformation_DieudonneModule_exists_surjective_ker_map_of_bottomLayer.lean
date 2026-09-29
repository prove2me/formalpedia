-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer
-- name    : Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/dcb6275d-89b9-5500-9855-544e77a3a50b
-- title:
--   Fontaine layer: ker M(π) surjects onto M(H_V)
-- statement:
--   Let $p$ be an odd prime and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative $\mathbb{Z}_{(p)}$-Hopf algebra, finite and free as a module and with cocommutative comultiplication, such that $H$ is a local ring and so is its Cartier dual, the $\mathbb{Z}_{(p)}$-dual module of $H$. Let $\kappa$ be a finite field of characteristic $p$, $N$ a finite-dimensional $\kappa$-vector space, and $\rho$ a monoid homomorphism from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the $\kappa$-linear endomorphisms of $N$. Assume given a bijection $e$ from the convolution monoid $\mathrm{Hom}_{\mathbb{Z}_{(p)}\text{-alg}}(H,\overline{\mathbb{Q}})$ to $N$ with $e(fg)=e(f)+e(g)$ and with $e(g)=\rho(\sigma)(e(f))$ whenever $g=\sigma\circ f$ pointwise, together with a family $\theta(a)$, $a\in\kappa$, of bialgebra endomorphisms of $H$ such that $g=f\circ\theta(a)$ forces $e(g)=a\cdot e(f)$. Let $V\subseteq N$ be a $\kappa$-subspace with $\rho(\sigma)V\subseteq V$ for all $\sigma$, let $H_V$ be a second finite free commutative cocommutative $\mathbb{Z}_{(p)}$-Hopf algebra, $\pi\colon H\to H_V$ a surjective bialgebra map, $e_V$ a bijection from $\mathrm{Hom}_{\mathbb{Z}_{(p)}\text{-alg}}(H_V,\overline{\mathbb{Q}})$ to $V$ with $e_V(f)=e(f\circ\pi)$ in $N$, and $\theta_V(a)$ bialgebra endomorphisms of $H_V$ with $\theta_V(a)\circ\pi=\pi\circ\theta(a)$. Assume further that $V\neq N$, and that in this case $N/V$ contains a $\kappa$-subspace $V'$ stable under the maps induced by the $\rho(\sigma)$ and a $\kappa$-linear isomorphism $\iota\colon V\to V'$ intertwining the actions of every $\sigma$ on $V$ and on $N/V$. Then, writing $M(-)$ for the Dieudonné module over $\mathbb{Z}/p$ (the colimit of the groups of additive elements in truncated Witt vectors) and $M(\pi_0)$ for the map induced by the base change $\mathbb{Z}/p\otimes_{\mathbb{Z}_{(p)}}\pi$, there exists an additive map $\lambda$ from $\ker M(\pi_0)$ to $M(\mathbb{Z}/p\otimes_{\mathbb{Z}_{(p)}}H_V)$ that is surjective and satisfies: for $x\in\ker M(\pi_0)$ whose image under Frobenius (respectively Verschiebung, respectively the map induced by $\mathbb{Z}/p\otimes\theta(a)$) again lies in $\ker M(\pi_0)$, the value of $\lambda$ at that image equals Frobenius (respectively Verschiebung, respectively the map induced by $\mathbb{Z}/p\otimes\theta_V(a)$) applied to $\lambda(x)$.
--
--   This is the Fontaine layer of Mazur's argument in Modular curves and the Eisenstein ideal II §14: the Hopf kernel of $\pi$ represents the quotient group scheme, its Dieudonné module is $\ker M(\pi_0)$, and the hypothesis on $V'$ produces inside that quotient a finite flat subgroup scheme isomorphic to $\operatorname{Spec}H_V$, whence the surjection $\lambda$ compatible with $F$, $V$ and the $\kappa$-multiplications. It is used in the bound on the rank of the Hecke-torsion at $j=0$ recorded in [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer.lean

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

theorem Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer
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
    (θ : κ → (H →ₐc[GaloisRep.ratLocalizedAt p] H))
    (hθ : ∀ (a : κ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (θ a h)) → e g = a • e f)
    (V : Submodule κ N)
    (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V)
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV) (hπ : Function.Surjective π)
    (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
    (heV : ∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ((eV f : ↥V) : N) =
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))))
    (θV : κ → (HV →ₐc[GaloisRep.ratLocalizedAt p] HV))
    (hθV : ∀ a : κ,
      (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hbot : V ≠ ⊤ →
      ∃ (V' : Submodule κ (N ⧸ V)) (ι : ↥V ≃ₗ[κ] ↥V'),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V',
          Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) x ∈ V') ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
          ((ι ⟨ρ σ v, hV σ v v.2⟩ : ↥V') : N ⧸ V) =
            Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) ((ι v : ↥V') : N ⧸ V))
    (hVtop : V ≠ ⊤) :
    ∃ lam : ↥(AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))) →+
        Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] HV),
      Function.Surjective lam ∧
      (∀ x (hx : Deformation.DieudonneModule.frobenius (ZMod p) p _ x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.frobenius (ZMod p) p _ (lam x)) ∧
      (∀ x (hx : Deformation.DieudonneModule.verschiebung (ZMod p) p _ x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (lam x)) ∧
      (∀ (a : κ) x (hx : Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θV a)) (lam x)) := by sorry
