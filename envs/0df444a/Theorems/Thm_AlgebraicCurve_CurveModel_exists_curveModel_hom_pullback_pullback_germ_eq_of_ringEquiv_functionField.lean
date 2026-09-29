-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
-- name    : AlgebraicCurve.CurveModel.exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/52558152-e216-5368-b969-171e75edb8fd
-- title:
--   Curve model of L on an iterated base change
-- statement:
--   Let $R_0$ be a commutative ring and let $\pi_X : X \to \operatorname{Spec} R_0$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically integral. Let $j : R_0 \to O$ be a ring homomorphism, $k$ an algebraically closed field, $i : O \to k$ a ring homomorphism, and $s : \operatorname{Spec} k \to \operatorname{Spec} R_0$ a morphism with $\operatorname{Spec}(i)$ followed by $\operatorname{Spec}(j)$ equal to $s$; assume the base change $X \times_{\operatorname{Spec} R_0, s} \operatorname{Spec} k$ is integral. Let $L$ be a field and a $k$-algebra, and let $e_L : L \cong K(X\times_s \operatorname{Spec} k)$ be a ring isomorphism carrying $\operatorname{algebraMap}_k^L(z)$, for $z \in k$, to the image of $z$ under `baseToFunctionField` of the second projection, i.e. the germ at the generic point of the image of $z$ under the structure morphism on global sections. The conclusion asserts the existence of a `CurveModel` $\mathfrak M$ for $k$ and $L$ — an integral scheme $\mathfrak M.C$ with a proper structure morphism $\mathfrak M.\mathrm{toBase} : \mathfrak M.C \to \operatorname{Spec} k$ that is smooth of relative dimension $1$, a ring isomorphism $\mathfrak M.\mathrm{ffEquiv} : L \cong K(\mathfrak M.C)$ compatible with constants from $k$ in the same sense, a bijection from the closed points of $\mathfrak M.C$ onto the places of $L/k$ (valuation subrings of $L$ containing $k$, proper and principal) matching each stalk with the corresponding valuation subring under $\mathfrak M.\mathrm{ffEquiv}^{-1}$, and the property that every finite subset of $\mathfrak M.C$ lies in an affine open — together with a morphism $e$ from $\mathfrak M.C$ to the iterated fibre product $(X \times_{\operatorname{Spec}R_0}\operatorname{Spec}O)\times_{\operatorname{Spec}O}\operatorname{Spec}k$ which is an isomorphism, such that $e$ followed by the second projection is $\mathfrak M.\mathrm{toBase}$, and such that for every open $U \subseteq X$ (with nonemptiness hypotheses on $U$, on its preimage in $X\times_s\operatorname{Spec}k$ and on its preimage in $\mathfrak M.C$) and every $t \in \Gamma(X,U)$, the germ at the generic point of the pull-back of $t$ along $e$ followed by the two first projections, read in $L$ through $\mathfrak M.\mathrm{ffEquiv}^{-1}$, equals $e_L^{-1}$ of the germ at the generic point of the pull-back of $t$ to $X\times_s\operatorname{Spec}k$ along the first projection.
--
--   A transport statement: it moves a curve model of the function field of the base change $X\times_s\operatorname{Spec}k$ onto the two-step base change $(X\times_{R_0}O)\times_O k$ and along a given identification of that function field with an abstract field $L$, retaining the compatibility of function-field identifications with germs of sections of $X$. It is used in the construction of Galois-equivariant curve models of Shimura curves, by [`CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_curveModel_iso_gal_baseChange`](thm.html#CerednikDrinfeld.ShimuraCurveModel.ModuliWitnessD.exists_curveModel_iso_gal_baseChange).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.exists_curveModel_hom_pullback_pullback_germ_eq_of_ringEquiv_functionField
    {R₀ : Type} [CommRing R₀] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of R₀))
    [IsProper πX] [SmoothOfRelativeDimension 1 πX] [GeometricallyIntegral πX]
    {O : Type} [CommRing O] (j : R₀ →+* O) (k : Type) [Field k] [IsAlgClosed k] (i : O →+* k)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R₀))
    (hs : Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom j) = s)
    [AlgebraicGeometry.IsIntegral ↑(pullback πX s)]
    {L : Type} [Field L] [Algebra k L] (eL : L ≃+* ↥((pullback πX s).functionField))
    (heL : ∀ z : k, eL (algebraMap k L z) = baseToFunctionField (pullback.snd πX s) z) :
    ∃ (𝔐 : AlgebraicCurve.CurveModel k L)
      (e : 𝔐.C ⟶ pullback (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)))
      (_ : IsIso e),
      e ≫ pullback.snd (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) = 𝔐.toBase ∧
      ∀ (U : X.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((pullback.fst πX s) ⁻¹ᵁ U))]
        [Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
          pullback.fst πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U))]
        (t : Γ(X, U)),
        𝔐.ffEquiv.symm (𝔐.C.germToFunctionField
          ((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
            pullback.fst πX (Spec.map (CommRingCat.ofHom j))) ⁻¹ᵁ U)
          (((e ≫ pullback.fst (pullback.snd πX (Spec.map (CommRingCat.ofHom j))) (Spec.map (CommRingCat.ofHom i)) ≫
            pullback.fst πX (Spec.map (CommRingCat.ofHom j))).app U).hom t)) =
        eL.symm ((pullback πX s).germToFunctionField ((pullback.fst πX s) ⁻¹ᵁ U) (((pullback.fst πX s).app U).hom t)) := by sorry
