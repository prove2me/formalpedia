-- Prove2me | Theorems.Thm_AlgebraicCurve_ker_productMap_eq_of_placeEquiv_restrictAlong
-- name    : AlgebraicCurve.ker_productMap_eq_of_placeEquiv_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/71bd151f-7135-5798-8162-05f0c426017c
-- title:
--   Tensor kernel determined by the induced bijection of places
-- statement:
--   Let $K$ be an algebraically closed field and let $E$, $F$, $F'$ be fields equipped with $K$-algebra structures, each of essentially finite type over $K$ and each a curve over $K$ in the sense of `IsCurveOver`: every nonzero element has a principal divisor (a divisor $D$ with $D(v)=\operatorname{ord}_v(f)$ at every place and $\deg D=0$), the residue field of every place is finite over $K$, and the module of Kähler differentials $\Omega_{\,\cdot\,/K}$ is free of rank one. Here a place of a $K$-algebra $L$ is a valuation subring of $L$ that contains the image of $K$, is not all of $L$, and is a principal ideal ring. Let $\varphi_0,\varphi_1 : E \to F$ and $\psi_0,\psi_1 : E \to F'$ be $K$-algebra homomorphisms, each integral as a ring homomorphism, and let $\theta : \mathrm{Place}(K,F) \simeq \mathrm{Place}(K,F')$ be a bijection of the sets of places such that for every place $R$ of $F$ and for $i = 0,1$, the restriction of $\theta(R)$ along $\psi_i$ (the place of $E$ whose valuation subring is the preimage of that of $\theta(R)$ under $\psi_i$) equals the restriction of $R$ along $\varphi_i$. Then the two $K$-algebra homomorphisms $E \otimes_K E \to F$, $x \otimes y \mapsto \varphi_0(x)\varphi_1(y)$, and $E \otimes_K E \to F'$, $x \otimes y \mapsto \psi_0(x)\psi_1(y)$, have the same kernel as ideals of $E \otimes_K E$.
--
--   A rigidity statement for correspondences between curves: the ideal of $E \otimes_K E$ cut out by a pair of integral maps to a curve — equivalently the correspondence on $E$ that the pair defines — depends only on the induced restriction maps on places, so two pairs whose places match under a bijection define the same correspondence. It is used in the Čerednik–Drinfel'd part of the development, in the construction of isomorphisms of moduli towers compatible with the given maps of function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ker_productMap_eq_of_placeEquiv_restrictAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem AlgebraicCurve.ker_productMap_eq_of_placeEquiv_restrictAlong
    {K E F F' : Type*} [Field K] [IsAlgClosed K] [Field E] [Field F] [Field F']
    [Algebra K E] [Algebra K F] [Algebra K F']
    [IsCurveOver K E] [Algebra.EssFiniteType K E] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ₀ φ₁ : E →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (ψ₀ ψ₁ : E →ₐ[K] F') (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (θ : Place K F ≃ Place K F')
    (hθ₀ : ∀ R : Place K F, (θ R).restrictAlong ψ₀ hψ₀ = R.restrictAlong φ₀ hφ₀)
    (hθ₁ : ∀ R : Place K F, (θ R).restrictAlong ψ₁ hψ₁ = R.restrictAlong φ₁ hφ₁) :
    RingHom.ker (Algebra.TensorProduct.productMap φ₀ φ₁).toRingHom =
      RingHom.ker (Algebra.TensorProduct.productMap ψ₀ ψ₁).toRingHom := by sorry
