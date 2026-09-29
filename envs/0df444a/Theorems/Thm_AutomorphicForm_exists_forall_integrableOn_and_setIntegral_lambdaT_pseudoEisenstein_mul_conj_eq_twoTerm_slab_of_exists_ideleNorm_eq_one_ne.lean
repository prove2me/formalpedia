-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_twoTerm_slab_of_exists_ideleNorm_eq_one_ne
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_twoTerm_slab_of_exists_ideleNorm_eq_one_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/3f86ee71-d12f-55ad-8683-13ff0159ca36
-- title:
--   Off-diagonal Maass–Selberg relation on a determinant slab
-- statement:
--   Let $F$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi_F$ be a set of elements of $\mathrm{GL}_2$ of the adele ring of $F$ (entering as the domain component of the carrier-pin package `productionPinsOf` built from the principal levels intersected with the finite-adelic subgroup, the Hecke generators at the finite places, and the adelic box). Write $\alpha_m$ for the idelic modulus, the character of $\mathbb{A}_F^\times$ obtained from `distribHaarChar` with values in $\mathbb{R}^\times$, and assume $\alpha_m$ is everywhere positive. Then there is a constant $c>0$ such that for all monoid homomorphisms $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ with: some idele $z$ of `ideleNorm` equal to $1$ and $\mu(z)\neq\nu(z)$; $|\mu(x)|=|\nu(x)|=1$ for all $x$; $\mu$ and $\nu$ trivial on the image of $F^\times$; for all $s,s'\in\mathbb{C}$ with $\operatorname{Re} s,\operatorname{Re} s'>1/2$; and for all $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ that are continuous, finite under the row-isometry subgroup at each infinite place, invariant under an open subgroup of the finite-adelic subgroup (the kernel of `glArch`), and satisfy the induction rule $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup, with $(\eta_1,\eta_2)=(\mu\,\alpha_m^{s+1/2},\ \nu\,\alpha_m^{-(s+1/2)})$ for $\varphi$ and the same with $s'$ for $\psi$, the following holds: there is $R_0$ such that for every $R\ge R_0$, writing $\Lambda^R$ for the truncation that subtracts, on the set where `adelicHeight` exceeds $e^R$, the constant term along the unipotent family $t\mapsto n(t)$ taken against the Borel σ-algebra and the Haar measure of $\mathbb{A}_F$ conditioned to the adelic box, and $E_\varphi(g)=\varphi(g)+\sum_{\xi\in F}\varphi(w\,n(\xi)g)$ for the pseudo-Eisenstein sum, the function $x\mapsto \Lambda^R E_\varphi(x)\,\overline{\Lambda^R E_\psi(x)}$ is integrable on `canonicalTruncationDomain F α β` for the Haar measure `adelicGLHaar`, and its integral there equals $$c\Big(\langle\varphi,\psi\rangle\frac{e^{R(s+\bar{s'})}}{s+\bar{s'}}-\langle M\varphi,M\psi\rangle\frac{e^{-R(s+\bar{s'})}}{s+\bar{s'}}\Big),$$ where $\langle\cdot,\cdot\rangle$ is the integral of $a(k)\overline{b(k)}$ over the adelic maximal compact subgroup against `maximalCompactHaar`, and $M\varphi(g)=\mathrm{vol}(\text{adelic box})^{-1}\int_{\mathbb{A}_F}\varphi(w^{-1}n(x)g)\,dx$ is the normalised Weyl intertwining integral.
--
--   This is the Maass–Selberg relation for truncated Eisenstein series on $\mathrm{GL}_2$ over a number field, restricted to a determinant slab $\alpha<|\det|<\beta$, in the off-diagonal case where $\mu/\nu$ is non-trivial on the norm-one ideles: only the two terms built from $\langle\varphi,\psi\rangle$ and $\langle M\varphi,M\psi\rangle$ appear, with no cross terms. It is cited by the statements that assemble the slab Maass–Selberg relations for pairs of characters, combining this case with the one in which the two characters agree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_twoTerm_slab_of_exists_ideleNorm_eq_one_ne.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_twoTerm_slab_of_exists_ideleNorm_eq_one_ne
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hoff : ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ μ z ≠ ν z)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re)
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
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s') ) := by sorry
