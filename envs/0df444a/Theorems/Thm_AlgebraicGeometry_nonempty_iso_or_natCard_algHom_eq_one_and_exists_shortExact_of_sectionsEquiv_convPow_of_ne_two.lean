-- Prove2me | Theorems.Thm_AlgebraicGeometry_nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two
-- name    : AlgebraicGeometry.nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/2958a460-b11e-527f-ab49-50e0d227ccf0
-- title:
--   Dichotomy for an odd flat Hopf model of μ_q
-- statement:
--   Let $p$ be a natural number (primality is not assumed) and let $q$ be a prime with $q \neq 2$. Let $K$ be a commutative Hopf algebra over $\mathbf Z$ that is of finite type and flat as a $\mathbf Z$-module, such that for every prime $\ell \neq p$ the base change $\mathbf Z_{(\ell)} \otimes_{\mathbf Z} K$ is a finite module over the subring $\mathbf Z_{(\ell)} \subset \mathbf Q$ of rationals whose denominator is coprime to $\ell$, such that $K$ has exactly $q$ $\mathbf Z$-algebra homomorphisms to $\overline{\mathbf Q} =$ `AlgebraicClosure ℚ`, and such that for every ring automorphism $\sigma$ of $\overline{\mathbf Q}$ and every $n_\sigma \in \mathbf N$ with $\sigma\zeta = \zeta^{n_\sigma}$ for all $\zeta$ with $\zeta^q = 1$, one has $\sigma \circ \psi = \psi^{n_\sigma}$ for every $\psi : K \to \overline{\mathbf Q}$, the power being taken in the convolution monoid `WithConv` of algebra homomorphisms. Let $L$ be an abelian sheaf on the small fppf site of $\operatorname{Spec}\mathbf Z$ (objects: schemes over $\operatorname{Spec}\mathbf Z$ whose structure morphism is flat and locally of finite presentation) together with additive isomorphisms $L(U) \cong \mathrm{Additive}(\mathrm{WithConv}(K \to_{\mathbf Z} \Gamma(U,\top)))$ for all such $U$, compatible with restriction in the sense that restriction along $f : U \to V$ corresponds to postcomposing a point of $K$ with $\Gamma(f)$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ in which the image of $p$ is a non-unit, and let $C$ be an abelian sheaf on the same site whose underlying presheaf is identified, via $iC$, with the restriction along the forgetful functor to $\mathbf{Sch}$ of the presheaf underlying $\mu_q = \ker(\text{$q$-power map on } \mathbf G_m)$ on the big fppf site. Then either $L$ and $C$ are isomorphic as sheaves, or $K$ has exactly one $A$-valued point and there exist an abelian sheaf $Q$ on the small fppf site and morphisms $f : L \to C$, $g : C \to Q$ with $f$ followed by $g$ zero, such that the resulting short complex is short exact and $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbf Z, Q)$ divides $q$.
--
--   This is the multiplicative-type half of the analysis of quasi-finite flat group schemes of odd prime order over $\operatorname{Spec}\mathbf Z$ that are finite away from one prime — admissible groups in Mazur's sense: such a model of $\mu_q$ is either $\mu_q$ itself or sits in $\mu_q$ with small cokernel cohomology. It is used by [`AlgebraicGeometry.exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two`](thm.html#AlgebraicGeometry.exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionFlag
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem AlgebraicGeometry.nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two
    (p : ℕ) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj) :
    Nonempty (L ≅ C) ∨
    (Nat.card (K →ₐ[ℤ] ↥A) = 1 ∧
      ∃ (Q : Sheaf (smallFppfTopology specInt) Ab.{1}) (f : L ⟶ C) (g : C ⟶ Q)
        (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
          Nat.card (fppfCohomology specInt Q 0) ∣ q) := by sorry
