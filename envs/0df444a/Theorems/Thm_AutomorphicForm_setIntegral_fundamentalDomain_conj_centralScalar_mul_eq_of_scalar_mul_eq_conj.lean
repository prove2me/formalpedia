-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
-- name    : AutomorphicForm.setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/4a47e32f-2ebc-553a-b54e-b2e01b2ebe03
-- title:
--   Scalar stabilising γ₀ leaves the centralizer-domain integral unchanged
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta\in\mathbb{R}$ with $0<\alpha$, and let $\gamma_0\in\mathrm{GL}_2(F)$. Write $\mathrm{GL}_2(\mathbb{A}_F)$ for [`AutomorphicForm.AdelicGL2 (𝓞 F) F`](def/AutomorphicForm_AdelicLsXi.html#L12), the general linear group of degree $2$ over the adele ring of $F$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, let `globalPoints` be the homomorphism $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_F)$ induced by $F\to\mathbb{A}_F$, and let `centralScalar` be the homomorphism $\mathbb{A}_F^\times\to\mathrm{GL}_2(\mathbb{A}_F)$ sending a unit to the corresponding scalar matrix. For an idele $x$, $\|x\|$ denotes `ideleNorm`, the module of $x$, i.e. the real number given by the distributive Haar character of $\mathbb{A}_F$ at $x$. Let $\Psi\subseteq\mathrm{GL}_2(\mathbb{A}_F)$ be contained in the band $\{g:\|\det g\|\in[\alpha,\beta]\}$ and be a fundamental domain for the action of the image under `globalPoints` of the centralizer of $\{\gamma_0\}$ in $\mathrm{GL}_2(F)$ on the restriction of `adelicGLHaar` to that band. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous with compact support, let $z\in\mathbb{A}_F^\times$, and let $s\in F^\times$, $h\in\mathrm{GL}_2(F)$ satisfy $\mathrm{scalar}(s)\,\gamma_0=h^{-1}\gamma_0 h$ in $\mathrm{GL}_2(F)$. Then, with $\hat s$ the principal idele attached to $s$, $$\int_{\Psi} f\bigl(x^{-1}\,\gamma_0\,(\hat s z)\,x\bigr)\,dx=\int_{\Psi} f\bigl(x^{-1}\,\gamma_0\,z\,x\bigr)\,dx,$$ both integrals being taken over $\Psi$ with respect to `adelicGLHaar`, with $\gamma_0$ read via `globalPoints` and the ideles $\hat s z$ and $z$ read as central scalar matrices.
--
--   This is the stabiliser-invariance property of the elliptic orbital integral attached to a class $\gamma_0$: twisting the central idele by a rational scalar $s$ that conjugates $\gamma_0$ to $s\gamma_0$ does not change the integral over a fundamental domain for the rational centralizer in a determinant band. It is used in the per-class unfolding of the elliptic contribution, where it feeds the computation of [`AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass`](thm.html#AutomorphicForm.finsum_sigmaCentralizerDomain_ellipticNorm_eq_mul_sum_finsum_centralizerDomain_elliptic_of_forall_perClass).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_conj_centralScalar_mul_eq_of_scalar_mul_eq_conj
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α)
    (γ₀ : GL (Fin 2) F)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (z : (AdeleRing (𝓞 F) F)ˣ)
    (s : Fˣ) (h : GL (Fin 2) F)
    (hsh : Matrix.GeneralLinearGroup.scalar (Fin 2) s * γ₀ = h⁻¹ * γ₀ * h) :
    ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) s * z) * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x in Ψ, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
        (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
