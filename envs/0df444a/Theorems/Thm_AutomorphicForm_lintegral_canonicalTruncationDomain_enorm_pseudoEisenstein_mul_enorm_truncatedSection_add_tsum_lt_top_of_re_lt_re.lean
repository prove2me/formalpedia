-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_canonicalTruncationDomain_enorm_pseudoEisenstein_mul_enorm_truncatedSection_add_tsum_lt_top_of_re_lt_re
-- name    : AutomorphicForm.lintegral_canonicalTruncationDomain_enorm_pseudoEisenstein_mul_enorm_truncatedSection_add_tsum_lt_top_of_re_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e2493bd4-b07e-5fcc-869b-1b93159b1037
-- title:
--   Finiteness of the truncated Rankin–Selberg integrand on the slab
-- statement:
--   Let $F$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha<\beta$. Write $\alpha_m$ for the homomorphism from the idele group $(\mathbb{A}_F)^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_F$ composed with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume $\alpha_m(x)>0$ for every $x$. Let $\mu,\nu,\mu',\nu'$ be homomorphisms $(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ which are unitary (of absolute value $1$ at every idele) and trivial on the principal ideles, let $s,s'\in\mathbb{C}$ satisfy $1/2<\operatorname{Re}s$, $1/2<\operatorname{Re}s'$ and $\operatorname{Re}s<\operatorname{Re}s'$, and let $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous functions that are `IsArchKFinite` (at each infinite place the right translates under the corresponding archimedean row-isometry subgroup span a finite-dimensional space) and `IsKfSmooth` (the stabiliser for right translation inside the kernel of the archimedean projection of $\mathrm{GL}_2(\mathbb{A}_F)$ is open), and which transform under the adelic Borel subgroup (lower-left entry zero) by $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ with $\eta_1=\mu\,\alpha_m^{\,s+1/2}$, $\eta_2=\nu\,\alpha_m^{-(s+1/2)}$, respectively by the same rule for $\psi$ with $\mu',\nu',s'$ in place of $\mu,\nu,s$. Let $R\in\mathbb{R}$. Put $E_\varphi(x)=\varphi(x)+\sum_{\xi\in F}\varphi(w\,n(\xi)\,x)$, where $w$ is the image of the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\cdot)$ the upper unipotent, $M\psi(y)=\int_{\mathbb{A}_F}\psi(w^{-1}n(t)y)\,dt$ for the additive adelic Haar measure, and $$\psi_R(y)=\begin{cases}\psi(y)&\text{if }\mathrm{ht}(y)\le e^R,\\-\,\mathrm{vol}(\text{adelic box})^{-1}M\psi(y)&\text{otherwise},\end{cases}$$ with $\mathrm{ht}$ the adelic height and the volume taken for the additive adelic Haar measure. Then the lower Lebesgue integral of $\|E_\varphi(x)\|\bigl(\|\psi_R(x)\|+\sum_{\xi\in F}\|\psi_R(w\,n(\xi)\,x)\|\bigr)$ over `canonicalTruncationDomain F α β`, the classically chosen truncation domain attached to $(\alpha,\beta)$, against the Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$, is finite.
--
--   This is the absolute-convergence input for the Rankin–Selberg unfolding of the pairing of an Eisenstein series $E_\varphi$ against the truncated section $\psi_R$ over the determinant slab $\alpha\le\|\det g\|\le\beta$, the truncation at height $e^R$ being Arthur's. It is invoked in the derivations of the Maass–Selberg relations and of the two-term and cross-term expressions for the slab integral of $\Lambda^R E_\psi$ against $E_\varphi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_canonicalTruncationDomain_enorm_pseudoEisenstein_mul_enorm_truncatedSection_add_tsum_lt_top_of_re_lt_re.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.lintegral_canonicalTruncationDomain_enorm_pseudoEisenstein_mul_enorm_truncatedSection_add_tsum_lt_top_of_re_lt_re
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμ' : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ') (_hν' : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν')
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμ'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ') (_hν'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν')
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re) (_hlt : s.re < s'.re)
      (φ : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ' αm hαm s') (AutomorphicForm.etaSnd ν' αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ)
      (R : ℝ),
    ∫⁻ x in AutomorphicForm.canonicalTruncationDomain F α β,
        ‖AutomorphicForm.pseudoEisenstein F φ x‖ₑ *
          (‖(if NumberField.AdelicHeight.adelicHeight F x ≤ Real.exp R then ψ x
              else -(((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ x))‖ₑ +
            ∑' ξ : F,
              ‖(if NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) ≤ Real.exp R
                then ψ (AutomorphicForm.adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)
                else -(((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                  AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ
                    (AutomorphicForm.adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞ := by sorry
