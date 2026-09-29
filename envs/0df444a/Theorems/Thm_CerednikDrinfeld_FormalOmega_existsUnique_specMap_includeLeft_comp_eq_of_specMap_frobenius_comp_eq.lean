-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
-- name    : CerednikDrinfeld.FormalOmega.existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f894adcd-4bc4-534c-ac13-23e2fcc2be8b
-- title:
--   Unique descent of morphisms along the Frobenius twist of Spec(B⊗𝒪̂^{nr})
-- statement:
--   Let $r$ be a prime and let $\mathcal O$ be a characteristic-zero domain which is a discrete valuation ring, $\pi\in\mathcal O$ irreducible, $\mathcal O$ complete for the $(\pi)$-adic topology, with $\#(\mathcal O/(\pi))=r$ and $(r)=(\pi)$. Let $Onr$ be a characteristic-zero domain which is an $\mathcal O$-algebra, equipped with an $\mathcal O$-algebra automorphism $Fr$, such that $Onr$ is complete for the $(\pi Onr)$-adic topology, $(\pi Onr)$ is maximal, every $x\in Onr$ satisfies a monic polynomial over $\mathcal O$ modulo $\pi Onr$, every monic polynomial over $Onr$ of positive degree has a root modulo $\pi Onr$, and $Fr(x)\equiv x^{r}\pmod{\pi Onr}$ for all $x$. Fix $m>0$, write $S$ for the subalgebra $\{x : (Fr^{m})(x)=x\}$ of $Onr$ (the equaliser of $Fr^{m}$ with the identity as $\mathcal O$-algebra maps), and let $FrS$ be an $S$-algebra automorphism of $Onr$ agreeing pointwise with $Fr^{m}$. Let $B$ be a commutative ring which is both an $\mathcal O$-algebra and an $S$-algebra, compatibly, with $\pi$ nilpotent in $B$. Then for every scheme $T$ and every morphism $f\colon \operatorname{Spec}(B\otimes_{S}Onr)\to T$ satisfying $f\circ\operatorname{Spec}(\mathrm{id}_B\otimes FrS)=f$, there is a unique morphism $g\colon\operatorname{Spec}B\to T$ with $g\circ\operatorname{Spec}(b\mapsto b\otimes 1)=f$.
--
--   This is the scheme-theoretic descent step for the Frobenius twist used in the Čerednik–Drinfeld uniformisation: a morphism out of $\operatorname{Spec}(B\otimes_S\widehat{\mathcal O}^{\mathrm{nr}})$ invariant under $1\otimes\mathrm{Fr}^{m}$ descends uniquely along the structure map, with no finiteness assumption on the target $T$. It is applied in [`CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_of_frobTwist_eq`](thm.html#CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_of_frobTwist_eq), where the same statement is packaged for families on a co-represented functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NumberField TensorProduct
open CategoryTheory AlgebraicGeometry CerednikDrinfeld
open CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.existsUnique_specMap_includeLeft_comp_eq_of_specMap_frobenius_comp_eq
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x)
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B] [IsScalarTower 𝒪 ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B]
    (hB : IsNilpotent (algebraMap 𝒪 B π))
    (T : Scheme.{0}) (f : Spec (CommRingCat.of (B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ⟶ T)
    (hf : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) B) (FrS : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)).toRingHom) ≫ f = f) :
    ∃! g : Spec (CommRingCat.of B) ⟶ T,
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr)) ≫ g = f := by sorry
