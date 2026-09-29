-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two
-- name    : AlgebraicGeometry.exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/fb5ce2a1-dafc-541c-abff-7cb4e9016a61
-- title:
--   A constant ℤ/q layer receiving an H¹_{fppf}-injective map
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, and let $K$ be a type equipped with a commutative ring structure, a Hopf algebra structure over $\mathbf Z$, finite type as a $\mathbf Z$-algebra and flat as a $\mathbf Z$-module. Assume: for every prime $\ell \neq p$, the tensor product $\mathbf Z_{(\ell)} \otimes_{\mathbf Z} K$ is a finite module over the subring $\mathbf Z_{(\ell)} \subset \mathbf Q$ of rationals whose denominator is coprime to $\ell$ ([`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8)); the set of $\mathbf Z$-algebra maps $K \to \overline{\mathbf Q}$ has cardinality exactly $q$; and every ring automorphism $\sigma$ of $\overline{\mathbf Q}$ fixes $\psi(k)$ for every such $\psi$ and every $k \in K$. Let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbf Z$, whose objects are $\operatorname{Spec}\mathbf Z$-schemes that are flat and locally of finite presentation, and suppose given, for each object $U$, an isomorphism of additive groups from $L(U)$ onto the additive group attached to the $\mathbf Z$-algebra maps $K \to \Gamma(U,\mathcal O_U)$ under convolution, these isomorphisms being compatible with restriction along any morphism $f : U \to V$ of the site, in the sense that the section $e_U(L(f)(s))$ is the composite of $e_V(s)$ with the map induced by $f$ on global sections. Then there exist a sheaf of abelian groups $C$ on the small fppf site of $\operatorname{Spec}\mathbf Z$, an isomorphism of the underlying presheaf of $C$ with the restriction, along the forgetful functor from the small fppf site to schemes, of the universe-lifted presheaf of continuous $\mathbf Z/q$-valued functions $\mathbf{Z}/q$ (`constantZModSheaf`), and a morphism $f : L \to C$ of sheaves such that the induced map on first fppf cohomology $H^1 \to H^1$ (the degree-one $\mathrm{Ext}$-groups of the sheaf category) is injective.
--
--   This is the comparison step which embeds a finite flat group-scheme-like "layer" of odd prime order $q$ over $\operatorname{Spec}\mathbf Z$, presented through its sheaf of $\mathbf Z$-algebra maps out of a Hopf algebra $K$, into the constant sheaf $\mathbf Z/q$ in a way that is injective on first fppf cohomology. It feeds the finiteness of $H^1_{\mathrm{fppf}}$ for such layers and, through that, the count of fppf cohomology of constant-kind primary torsion layers on the Néron model of $J_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionFlag
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem AlgebraicGeometry.exists_hom_restriction_constantZMod_fppfCohomologyMap_injective_of_sectionsEquiv_of_ne_two
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
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k)) :
    ∃ (C : Sheaf (smallFppfTopology specInt) Ab.{1})
      (_ : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
          (FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} q)).obj)
      (f : L ⟶ C), Function.Injective (fppfCohomologyMap specInt f 1) := by sorry
