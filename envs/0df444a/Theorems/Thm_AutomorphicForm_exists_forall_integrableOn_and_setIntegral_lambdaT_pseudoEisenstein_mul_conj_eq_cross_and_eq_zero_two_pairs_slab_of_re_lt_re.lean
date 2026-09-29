-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_cross_and_eq_zero_two_pairs_slab_of_re_lt_re
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_cross_and_eq_zero_two_pairs_slab_of_re_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/d9ffdae4-56e5-5861-b001-ed862a77f0e0
-- title:
--   Truncated inner products of GL₂ Eisenstein series: cross and vanishing cases
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_F$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ denotes the adele ring of $F$ and $\mathrm{GL}_2(\mathbb{A}_F)$ is `AdelicGL2 (𝓞 F) F`. Write $\alpha_m \colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ for the homomorphism obtained from `distribHaarChar (AdeleRing (𝓞 F) F)` by pushing its values along $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units (the idelic modulus), the adele ring carrying its Borel $\sigma$-algebra, and let $h_{\alpha m}$ be the hypothesis that $\alpha_m(x)>0$ for every idele $x$.
--
--   Under these hypotheses there exist a real constant $c>0$ and a real threshold $R_0$ — depending only on $F$, $\alpha$, $\beta$, $\Phi_F$ and the fixed measures, and in particular independent of all the data listed next — such that the following holds for all quadruples of characters and all sections as follows.
--
--   The data: four monoid homomorphisms $\mu,\nu,\mu',\nu' \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$; the unitarity hypotheses, asserting that each of $\mu,\nu,\mu',\nu'$ has $|\chi(x)|=1$ for every idele $x$; the idele-class hypotheses, asserting that each of $\mu,\nu,\mu',\nu'$ is trivial on the image of $F^\times$ in $\mathbb{A}_F^\times$; complex numbers $s,s'$ with $1/2<\operatorname{Re}s$, $1/2<\operatorname{Re}s'$ and $\operatorname{Re}s<\operatorname{Re}s'$; a function $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is an induced section for the pair $(\mu\,\alpha_m^{\,s+1/2},\ \nu\,\alpha_m^{-(s+1/2)})$, that is, $\varphi(bg)=\mu(b_{11})\alpha_m(b_{11})^{s+1/2}\,\nu(b_{22})\alpha_m(b_{22})^{-(s+1/2)}\,\varphi(g)$ for every $b$ in the adelic Borel subgroup (upper triangular invertible matrices) and every $g$, and which is continuous, archimedean $K$-finite (at each infinite place the right translates of $\varphi$ under the local row-isometry subgroup span a finite-dimensional space) and $K_f$-smooth (the stabiliser of $\varphi$ for right translation inside the subgroup of elements with trivial archimedean part is open); and a function $\psi$ subject to the same four conditions with $(\mu',\nu',s')$ in place of $(\mu,\nu,s)$.
--
--   For the conclusion, write $E_\varphi$ for `pseudoEisenstein F φ`, namely $E_\varphi(g)=\varphi(g)+\sum_{\xi\in F}\varphi(w\,n(\xi)\,g)$ with $w$ the adelic Weyl element and $n(\xi)$ the upper unipotent matrix with entry $\xi$, and similarly for $E_\psi$. For a real $R$ let $\Lambda^R$ denote the truncation operator `lambdaT` at height $\exp R$: $(\Lambda^R f)(g)=f(g)-\mathbf{1}_{\{\,\mathrm{ht}(g)>\exp R\,\}}(g)\cdot\int f(n(x)g)\,d\nu_{\mathrm{box}}(x)$, where $\mathrm{ht}$ is the adelic height [`NumberField.AdelicHeight.adelicHeight F`](def/NumberField_AdelicHeight.html#L158) and $\nu_{\mathrm{box}}$ is the measure component of the record `productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`, that is, additive Haar measure on $\mathbb{A}_F$ conditioned on the box `adelicBox F`, taken with respect to the Borel $\sigma$-algebra on $\mathbb{A}_F$. Integration over the group is with respect to `adelicGLHaar (Fin 2) (𝓞 F) F` over the domain `canonicalTruncationDomain F α β`, the third component of the canonically chosen truncation datum attached to $\alpha,\beta$ (empty if no such datum exists). Finally, $\int_{\mathbf K}$ denotes integration over the adelic maximal compact subgroup (elements whose finite part is integral and whose archimedean components are row isometries) against `maximalCompactHaar F`, and $M$ denotes the normalised Weyl intertwining integral $g\mapsto \mathrm{vol}(\mathrm{box})^{-1}\int_{\mathbb{A}_F}(\,\cdot\,)(w^{-1}n(x)g)\,dx$, the volume being that of `adelicBox F` for additive adelic Haar measure.
--
--   Then for every real $R$ with $R_0\le R$ both of the following hold.
--
--   First (the reversed-pair, or cross, case): if $\mu'=\nu$, $\nu'=\mu$ and there exists a norm-one idele $z$ (an element of the kernel of `distribHaarChar`) with $\mu(z)\ne\nu(z)$, then the function $g\mapsto (\Lambda^R E_\varphi)(g)\cdot\overline{(\Lambda^R E_\psi)(g)}$ is integrable on `canonicalTruncationDomain F α β`, and
--   $$\int_{\Phi_0}(\Lambda^R E_\varphi)\,\overline{\Lambda^R E_\psi} = c\left(\Big(\int_{\mathbf K}\varphi(k)\,\overline{(M\psi)(k)}\,dk\Big)\frac{e^{R(s-\overline{s'})}}{s-\overline{s'}} -\Big(\int_{\mathbf K}(M\varphi)(k)\,\overline{\psi(k)}\,dk\Big)\frac{e^{-R(s-\overline{s'})}}{s-\overline{s'}}\right),$$
--   where $\Phi_0$ is the truncation domain and $M\varphi$, $M\psi$ are the normalised intertwining integrals described above.
--
--   Second (the non-associate case): if there exists a norm-one idele $z$ with $\mu'(z)\ne\mu(z)$ or $\nu'(z)\ne\nu(z)$, and there exists a norm-one idele $z$ with $\mu'(z)\ne\nu(z)$ or $\nu'(z)\ne\mu(z)$, then again $g\mapsto(\Lambda^R E_\varphi)(g)\cdot\overline{(\Lambda^R E_\psi)(g)}$ is integrable on `canonicalTruncationDomain F α β`, and its integral over that domain is $0$.
--
--   This is the two-pair part of Langlands' inner product formula for truncated Eisenstein series on $\mathrm{GL}_2$ over a number field, truncated at a single height $e^R$ and restricted to a determinant slab $\alpha<|\det|<\beta$, in the range $\operatorname{Re}s<\operatorname{Re}s'$ where the unfolding converges absolutely: for reversed pairs of inducing characters only the two boundary (cross) terms survive, and for pairs that are associate to neither $(\mu,\nu)$ nor $(\nu,\mu)$ the truncated inner product vanishes. It feeds the assembly of the Maass–Selberg relations along the critical axis used in the spectral analysis of the Eisenstein part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_cross_and_eq_zero_two_pairs_slab_of_re_lt_re.lean

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
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_cross_and_eq_zero_two_pairs_slab_of_re_lt_re
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμ' : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ') (_hν' : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν')
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμ'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ') (_hν'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν')
      (s s' : ℂ) (_hs : 1 / 2 < s.re) (_hs' : 1 / 2 < s'.re) (_hlt : s.re < s'.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ) (_hφK : AutomorphicForm.IsArchKFinite F φ) (_hφf : AutomorphicForm.IsKfSmooth F φ)
      (ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ' αm hαm s') (AutomorphicForm.etaSnd ν' αm hαm s') ψ)
      (_hψc : Continuous ψ) (_hψK : AutomorphicForm.IsArchKFinite F ψ) (_hψf : AutomorphicForm.IsKfSmooth F ψ),
    ∀ R : ℝ, R₀ ≤ R →
      (μ' = ν → ν' = μ → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
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
        ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') )) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ' z ≠ μ z ∨ ν' z ≠ ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ' z ≠ ν z ∨ ν' z ≠ μ z) →
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
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = 0) := by sorry
