-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_roof_package_of_surjective
-- name    : AlgebraicCurve.Pic0.roof_package_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/4212c2fb-acb7-51a7-aa91-9ffb3c2be4c5
-- title:
--   Roof package along a surjective leg of function fields
-- statement:
--   Let $K$ be a field of characteristic zero and let $F_0,F_1,F_2$ be fields with $K$-algebra structures, where $F_1$ and $F_2$ satisfy `HasPrincipalDivisors`: every nonzero element $f$ admits a divisor of degree $0$ whose value at each place is $\mathrm{ord}_v(f)$ (places being the proper valuation subrings containing the image of $K$ that are principal ideal rings, divisors being finitely supported $\mathbb{Z}$-valued functions on them). Let $\iota\colon F_1\to F_2$ be a $K$-algebra map whose underlying ring map is integral and satisfies the predicate `FundamentalIdentityAlong` for the $F_1$-algebra structure on $F_2$ it induces, and assume $\iota$ is surjective; let $\alpha\colon F_0\to F_1$ be a $K$-algebra map with integral underlying ring map such that $\iota\circ\alpha$ is also integral; let $W$ be a $K$-automorphism of $F_1$. Then: (i) $\iota_*\iota^*D=D$ for every divisor $D$ of $F_1$; (ii) the induced map $\iota^*\colon \mathrm{Pic}^0(F_1)\to\mathrm{Pic}^0(F_2)$ on degree-zero divisors modulo principal ones is surjective; (iii) $(\iota\circ\alpha)_*\iota^*D=\alpha_*D$ for every divisor $D$ of $F_1$; and (iv) there is a $K$-automorphism $\theta$ of $F_2$ with $\theta(\iota a)=\iota(W^{-1}a)$ for all $a\in F_1$, such that the semilinear automorphism $(\theta,1)$ acting on $\mathrm{Pic}^0(F_2)$ satisfies $(\theta,1)\cdot\iota^*x=\iota^*\big((W^{-1},1)\cdot x\big)$ for every $x\in\mathrm{Pic}^0(F_1)$.
--
--   This bundles the four divisor-theoretic facts needed for a degree-one roof of function fields: push-forward undoes pull-back, the pull-back on degree-zero divisor classes is onto, push-forwards compose through the roof, and automorphisms of the base transport through it. It is used in the proof of the level-$\Gamma_H$ Hecke operator identity [`ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand`](thm.html#ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand), where $\iota$ is an inclusion of $q$-expansion fields that happens to be onto.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_roof_package_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_ShimuraKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.roof_package_of_surjective
    {K F₀ F₁ F₂ : Type} [Field K] [CharZero K] [Field F₀] [Field F₁] [Field F₂]
    [Algebra K F₀] [Algebra K F₁] [Algebra K F₂]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
    (ι : F₁ →ₐ[K] F₂) (hι : ι.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K ι hι)
    (hιs : Function.Surjective ι)
    (α : F₀ →ₐ[K] F₁) (hα : α.toRingHom.IsIntegral) (hια : (ι.comp α).toRingHom.IsIntegral)
    (W : F₁ ≃ₐ[K] F₁) :
    (∀ D : Divisor K F₁, Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι D) = D) ∧
    Function.Surjective (Pic0.pullbackAlongHom ι hι hFI) ∧
    (∀ D : Divisor K F₁,
      Divisor.pushforwardAlong (ι.comp α) hια (Divisor.pullbackAlong ι hι D) = Divisor.pushforwardAlong α hα D) ∧
    ∃ θ : F₂ ≃ₐ[K] F₂, (∀ a : F₁, θ (ι a) = ι (W.symm a)) ∧
      ∀ x₁ : Pic0 K F₁,
        SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFI x₁ =
          Pic0.pullbackAlongHom ι hι hFI (SemilinearAut.ofAlgAut W.symm • x₁) := by sorry
