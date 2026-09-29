-- Prove2me | Theorems.Thm_AlgebraicGeometry_nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two
-- name    : AlgebraicGeometry.nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/5d2bd71d-3916-5d8d-a051-55f63e6f92b8
-- title:
--   Fppf points sheaf of an odd flat ℤ/q-model over ℤ
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, and let $K$ be a commutative ring carrying a Hopf algebra structure over $\mathbf Z$ which is of finite type and flat as a $\mathbf Z$-algebra, subject to three further hypotheses: for every prime $\ell \neq p$ the module $\mathbf Z_{(\ell)} \otimes_{\mathbf Z} K$ is finite over $\mathbf Z_{(\ell)}$, where $\mathbf Z_{(\ell)}$ is realised as the subring of rationals whose denominator is coprime to $\ell$ ([`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8)); the set of $\mathbf Z$-algebra maps $K \to \overline{\mathbf Q}$ has cardinality exactly $q$; and every ring automorphism $\sigma$ of $\overline{\mathbf Q}$ satisfies $\sigma(\psi(k)) = \psi(k)$ for all such $\psi$ and all $k \in K$. Let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbf Z$ — objects are schemes over $\operatorname{Spec}\mathbf Z$ whose structure morphism is flat and locally of finite presentation — together with additive equivalences $e_U : L(U) \simeq \mathrm{Hom}_{\mathbf Z\text{-}\mathrm{alg}}(K, \Gamma(U, \mathcal O))$, the target being the points group of $K$ under convolution (`WithConv`, written additively), and assume these equivalences are natural: for $f : U \to V$ in the site, a section $s$ over $V$ and $k \in K$, the algebra map attached to the restriction of $s$ sends $k$ to the image of $(e_V s)(k)$ under $\Gamma(f)$. Let $C$ be a sheaf of abelian groups on the same site whose underlying presheaf is isomorphic to the restriction along the forgetful functor to schemes of the universe-lifted constant fppf sheaf $\mathbf Z/q$, whose sections over a scheme $X$ are the continuous maps $X \to \mathbf Z/q$. Then either $L$ and $C$ are isomorphic as sheaves, or there exist a sheaf $Q$ of abelian groups on the small fppf site and morphisms $f : L \to C$, $g : C \to Q$ with $f$ followed by $g$ zero such that $0 \to L \to C \to Q \to 0$ is short exact and the induced map $H^0(g)$ on degree-zero fppf cohomology over $\operatorname{Spec}\mathbf Z$ is surjective.
--
--   This is the dichotomy, in the style of Mazur's treatment of admissible group schemes of prime order over $\operatorname{Spec}\mathbf Z$ and of the Oort–Tate classification, between a flat $\mathbf Z$-model of $\mathbf Z/q$ being globally constant and being a subsheaf of the constant sheaf whose cokernel is concentrated away from the good primes. It feeds the construction of a morphism from the points sheaf to the constant $\mathbf Z/q$ sheaf with injective effect on fppf cohomology, in [`AlgebraicGeometry.exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two`](thm.html#AlgebraicGeometry.exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionFlag
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem AlgebraicGeometry.nonempty_iso_or_exists_shortExact_of_sectionsEquiv_algHom_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (hnat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (L.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (C : Sheaf (smallFppfTopology specInt) Ab.{1})
    (iC : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
      (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)).obj) :
    Nonempty (L ≅ C) ∨
    ∃ (Q : Sheaf (smallFppfTopology specInt) Ab.{1}) (f : L ⟶ C) (g : C ⟶ Q)
      (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact ∧
        Function.Surjective (fppfCohomologyMap specInt g 0) := by sorry
