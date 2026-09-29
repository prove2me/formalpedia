-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/abdf1548-7fa1-53e2-9df2-67d7ac575620
-- title:
--   Slab Maass–Selberg relation in the range Re s<Re s'
-- statement:
--   Let $F$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi_F$ be a subset of $\mathrm{GL}_2$ of the adele ring of $F$. Write $\alpha_m$ for the module character, the composite of the distributive Haar character of the adele ring with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, viewed as a homomorphism from the ideles to $\mathbb{R}^\times$, and assume $\alpha_m$ takes positive values. The assertion is the existence of a real $c>0$ and a real $R_0$, both independent of the data that follow, such that for all characters $\mu,\nu$ of the ideles with values in $\mathbb{C}^\times$ with $\mu=\nu$, both unitary ($\lVert\chi(x)\rVert=1$ for every idele $x$) and trivial on the principal ideles, for all $s,s'$ with $\mathrm{Re}\,s>1/2$, $\mathrm{Re}\,s'>1/2$, $s\neq\overline{s'}$ and $\mathrm{Re}\,s<\mathrm{Re}\,s'$, and for all $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ that are continuous, arch-$K$-finite (at each infinite place the right translates under the row-isometry subgroup span a finite-dimensional space), smooth for the finite part (the stabiliser under right translation by the kernel of the archimedean projection is open), and satisfy the induced-section identity $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for upper triangular $b$ with $(\eta_1,\eta_2)=(\mu\,\alpha_m^{s+1/2},\nu\,\alpha_m^{-(s+1/2)})$ for $\varphi$ and the same pair formed from $s'$ for $\psi$, the following holds for every $R\ge R_0$. Let $E_\varphi(g)=\varphi(g)+\sum_{\xi\in F}'\varphi(w\,u(\xi)g)$ be the pseudo-Eisenstein series, $u(t)$ the upper unipotent matrix with entry $t$ and $w$ the adelic Weyl element, and let $\Lambda^{T}f(g)=f(g)-\mathbf{1}_{\{\,\mathrm{ht}(g)>T\,\}}(g)\int f(u(t)g)\,dt$ be the truncation at $T=e^{R}$, where $\mathrm{ht}$ is the adelic height and the integral is against the additive adelic Haar measure conditioned on the adelic box. Then $x\mapsto \Lambda^{e^R}E_\varphi(x)\,\overline{\Lambda^{e^R}E_\psi(x)}$ is integrable on the canonical truncation domain attached to $(\alpha,\beta)$ for the Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$, and its integral over that domain equals $c$ times $$\frac{\langle\varphi,\psi\rangle_K e^{R(s+\overline{s'})}}{s+\overline{s'}}-\frac{\langle M\varphi,M\psi\rangle_K e^{-R(s+\overline{s'})}}{s+\overline{s'}}+\frac{\langle\varphi,M\psi\rangle_K e^{R(s-\overline{s'})}}{s-\overline{s'}}-\frac{\langle M\varphi,\psi\rangle_K e^{-R(s-\overline{s'})}}{s-\overline{s'}},$$ where $\langle f,h\rangle_K=\int_K f(k)\overline{h(k)}\,dk$ is taken over the adelic maximal compact subgroup with its Haar measure, and $Mf(g)=\mathrm{vol}(\text{box})^{-1}\int f(w^{-1}u(x)g)\,dx$ is the Weyl intertwining integral normalised by the real volume of the adelic box.
--
--   This is the Maass–Selberg relation for the inner product of two truncated Eisenstein series on $\mathrm{GL}_2$ over a number field, restricted to the slab of determinant norm between $\alpha$ and $\beta$, in the diagonal case $\mu=\nu$ and in the parameter range where the unfolding of the pseudo-Eisenstein series converges absolutely, with the truncation threshold $R_0$ uniform in the section data. It feeds [`AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab`](thm.html#AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab), where the restriction $\mathrm{Re}\,s<\mathrm{Re}\,s'$ is removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab_of_re_lt_re
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hμν : μ = ν)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re) (_hne : s ≠ conj s') (_hlt : s.re < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s') (AutomorphicForm.etaSnd ν αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R : ℝ, R₀ ≤ R →
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
