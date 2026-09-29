-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ea78e136-e0f3-544c-94fd-a57f521954d6
-- title:
--   Maass–Selberg relation on a determinant slab, diagonal case
-- statement:
--   Let $F$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi F$ be a set of adelic $2\times 2$ invertible matrices; write $\alpha_m:\mathbb{A}_F^\times\to\mathbb{R}^\times$ for the character obtained from the module $\mathrm{distribHaarChar}$ of the adele ring, and assume $\alpha_m$ takes positive values. Then there is a constant $c>0$ such that for all characters $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ with $\mu=\nu$, both of absolute value $1$ everywhere and both trivial on the image of $F^\times$, for all $s,s'$ with $\operatorname{Re} s>1/2$, $\operatorname{Re} s'>1/2$ and $s\neq\overline{s'}$, and for all continuous $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ upper triangular with $(\eta_1,\eta_2)=(\mu\,\alpha_m^{s+1/2},\nu\,\alpha_m^{-(s+1/2)})$, and $\psi$ likewise at $s'$, each being finite under right translation by the row-isometry subgroups at the infinite places and having open stabiliser in the subgroup of matrices with trivial archimedean component, there exists $R_0$ with the following property for every $R\ge R_0$. Let $E_\varphi(g)=\varphi(g)+\sum_{\xi\in F}\varphi(w\,n(\xi)g)$, let $\Lambda^{e^R}$ subtract from a function the indicator of $\{\,\mathrm{adelicHeight}>e^R\,\}$ times its constant term along $n(\mathbb{A}_F)$, computed against additive Haar measure conditioned to the adelic box (the parameters $\Phi F$ and the level and Hecke data enter only through this measure packaging), and let $M\varphi(g)=\mathrm{vol}(\text{box})^{-1}\int_{\mathbb{A}_F}\varphi(w^{-1}n(x)g)\,dx$. Then $x\mapsto \Lambda^{e^R}E_\varphi(x)\,\overline{\Lambda^{e^R}E_\psi(x)}$ is integrable on the canonical truncation domain attached to $(\alpha,\beta)$ for the Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$, and its integral there equals
--   $$c\Big(\langle\varphi,\psi\rangle\tfrac{e^{R(s+\overline{s'})}}{s+\overline{s'}}-\langle M\varphi,M\psi\rangle\tfrac{e^{-R(s+\overline{s'})}}{s+\overline{s'}}+\langle\varphi,M\psi\rangle\tfrac{e^{R(s-\overline{s'})}}{s-\overline{s'}}-\langle M\varphi,\psi\rangle\tfrac{e^{-R(s-\overline{s'})}}{s-\overline{s'}}\Big),$$
--   where $\langle a,b\rangle=\int a(k)\overline{b(k)}\,dk$ over the adelic maximal compact subgroup with its Haar measure. The constant $c$ is independent of $\mu,\nu,s,s',\varphi,\psi$, while the threshold $R_0$ may depend on them.
--
--   This is the Maass–Selberg relation for $\mathrm{GL}_2$ over a number field, in the diagonal case $\mu=\nu$, in the form of an exact four-term evaluation of the inner product of two truncated Eisenstein series over a determinant slab, valid for truncation parameters beyond a threshold. It feeds the results that continue this inner product in $s,s'$ to the unitary axis and extract from it the two-term and cross-term forms used in the spectral decomposition of the Eisenstein part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hμν : μ = ν)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re) (_hne : s ≠ conj s')
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s') (AutomorphicForm.etaSnd ν αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (c : ℂ) *
        ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ) := by sorry
