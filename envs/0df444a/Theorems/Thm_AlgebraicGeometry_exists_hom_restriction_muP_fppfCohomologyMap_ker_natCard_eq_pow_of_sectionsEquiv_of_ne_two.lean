-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
-- name    : AlgebraicGeometry.exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/04ac6d40-0a3f-5213-88f5-36d6a8d1bbb2
-- title:
--   Kernel on fppf H¹ of a μ_q-comparison map over Spec ℤ
-- statement:
--   Let $p$ be a natural number and $q$ a prime with $q \neq 2$, and let $K$ be a commutative ring equipped with a Hopf algebra structure over $\mathbf{Z}$ which is of finite type and flat as a $\mathbf{Z}$-algebra, and such that for every prime $\ell \neq p$ the tensor product $\mathbf{Z}_{(\ell)} \otimes_{\mathbf{Z}} K$ is a finite module over $\mathbf{Z}_{(\ell)}$, the ring of rationals whose denominator is coprime to $\ell$. Assume the set of $\mathbf{Z}$-algebra maps $K \to \overline{\mathbf{Q}}$ has exactly $q$ elements, and that for every ring automorphism $\sigma$ of $\overline{\mathbf{Q}}$ and every $n_\sigma$ with $\sigma\zeta = \zeta^{n_\sigma}$ for all $q$-th roots of unity $\zeta$, one has $\sigma \circ \psi = \psi^{n_\sigma}$ for every $\psi \colon K \to \overline{\mathbf{Q}}$, the power being taken in the convolution monoid structure `WithConv` on such maps. Let $L$ be a sheaf of abelian groups on the small fppf site of $\mathrm{Spec}\,\mathbf{Z}$ (objects: schemes over $\mathrm{Spec}\,\mathbf{Z}$ whose structure morphism is flat and locally of finite presentation), together with additive isomorphisms $L(U) \cong (K \to_{\mathbf{Z}\text{-alg}} \Gamma(U, \mathcal{O}))$, taken with the convolution group law, that are natural in $U$ in the sense that restriction along $f \colon U \to V$ corresponds to postcomposition with $\Gamma(f)$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ in which the image of $p$ is a nonunit, and let $d_t$ be such that the number of $\mathbf{Z}$-algebra maps $K \to A$ equals $q^{d_t}$. Then there exist $d_k$ with $d_k + d_t \le 1$, a sheaf $C$ of abelian groups on the small fppf site of $\mathrm{Spec}\,\mathbf{Z}$ whose underlying presheaf is isomorphic to the restriction, along the forgetful functor to schemes, of the underlying presheaf of [`FppfKummerSES.muPAbelianSheafLifted q`](def/AlgebraicGeometry_FppfKummerProp17.html#L608) (the kernel of the $q$-th power map on the multiplicative-group sheaf on the big fppf site, i.e. $\mu_q$), and a morphism $f \colon L \to C$ such that the kernel of the induced map on first fppf cohomology has exactly $q^{d_k}$ elements.
--
--   The statement is the counting step in the analysis of a multiplicative-kind layer of a finite flat group scheme of order $q$ over $\mathbf{Z}$: such a scheme is compared with $\mu_q$ in the style of the Oort–Tate classification, and the discrepancy is measured by the kernel of the comparison map on fppf $H^1$. It is used in the finiteness statement for first fppf cohomology of such layer models and in the multiplicative-kind case of the torsion-flag analysis for the Néron model of $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionFlag
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem AlgebraicGeometry.exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
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
    (dt : ℕ) (hKA : Nat.card (K →ₐ[ℤ] ↥A) = q ^ dt) :
    ∃ dk : ℕ, dk + dt ≤ 1 ∧
      ∃ (C : Sheaf (smallFppfTopology specInt) Ab.{1})
        (_ : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
            (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
        (f : L ⟶ C), Nat.card ↥(fppfCohomologyMap specInt f 1).ker = q ^ dk := by sorry
