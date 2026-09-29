-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/55bbb39e-7ef6-55dc-b478-6312872b8386
-- title:
--   Increment form of the GL₂ Maass–Selberg relations on a slab
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real numbers with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`), and let $\Phi_F$ be a set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ denotes `AdeleRing (𝓞 F) F` and `AdelicGL2 (𝓞 F) F` its group of invertible $2\times 2$ matrices. Write $\alpha_m \colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ for the homomorphism obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F)` of the adele ring by composing with the map $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units, the adele ring being equipped with its Borel $\sigma$-algebra `adeleBorel`; that is, $\alpha_m(x)$ is the factor by which multiplication by the idele $x$ scales additive Haar measure on $\mathbb{A}_F$. Assume the hypothesis `hαm`, that $\alpha_m(x)>0$ as a real number for every idele $x$.
--
--   The assertion is the existence of a real constant $c>0$ and a real threshold $R_0$, depending only on $F$, $\alpha$, $\beta$, $\Phi_F$ and the fixed measures, such that the following holds for all the data described next.
--
--   Data and hypotheses. Two homomorphisms $\mu,\nu\colon\mathbb{A}_F^\times\to\mathbb{C}^\times$ are given, subject to: `_hμ`, `_hν`, unitarity, i.e. $\lVert\chi(x)\rVert=1$ for every idele $x$; and `_hμF`, `_hνF`, triviality on principal ideles, i.e. $\chi(\iota(u))=1$ for every $u\in F^\times$, where $\iota$ is induced by $F\to\mathbb{A}_F$. Two complex numbers $s,s'$ are given with $\operatorname{Re} s>1/2$ (`_hs`) and $\operatorname{Re} s'>1/2$ (`_hs'`). Two functions $\varphi,\psi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ are given. The hypothesis `_hφ` says that $\varphi$ is an induced section for the pair of characters $\mathrm{etaFst}(\mu,\alpha_m,s)=\mu\cdot\alpha_m^{\,s+1/2}$ and $\mathrm{etaSnd}(\nu,\alpha_m,s)=\nu\cdot\alpha_m^{\,-(s+1/2)}$, where $\alpha_m^{\,w}(x)=\alpha_m(x)^w$ is the complex power `cpowChar`: for every $b$ in the adelic Borel subgroup (invertible matrices whose lower-left entry vanishes) and every $g$,
--   $$\varphi(bg)=\bigl(\mu\cdot\alpha_m^{\,s+1/2}\bigr)(b_{00})\,\bigl(\nu\cdot\alpha_m^{\,-(s+1/2)}\bigr)(b_{11})\,\varphi(g).$$
--   Further, `_hφc` asserts that $\varphi$ is continuous; `_hφK` that $\varphi$ satisfies `IsArchKFinite`, i.e. for every infinite place $w$ of $F$ the right translates of $\varphi$ under `archRowIsometrySubgroup F w` satisfy `RightTranslatesSpanFinite`; and `_hφf` that $\varphi$ satisfies `IsKfSmooth`, i.e. the stabiliser of $\varphi$, regarded as an element of `RightTranslationFn`, in the subgroup `finiteAdelicGL2Subgroup F` (the kernel of the archimedean component map `glArch`) is open. The hypotheses `_hψ`, `_hψc`, `_hψK`, `_hψf` are the same four conditions for $\psi$, with $s$ replaced by $s'$.
--
--   Notation for the conclusion. For a real number $T$ and $f\colon\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, let $\Lambda^T f$ denote `lambdaT` formed from: the measurable space and measure recorded in the fields `nS` and `ν` of `productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`, namely the Borel $\sigma$-algebra of $\mathbb{A}_F$ and the conditioning of the additive Haar measure `adelicAddHaar (𝓞 F) F` to the box `adelicBox F`; the unipotent family $x\mapsto$ `unipotentGL2` $x$; the height `adelicHeight F`; and the threshold $T$. Thus $\Lambda^T f(g)=f(g)-\mathbf{1}_{\{g\,:\,T<\mathrm{adelicHeight}_F(g)\}}(g)\cdot \mathrm{constantTerm}(f)(g)$, the constant term being the integral over $\mathbb{A}_F$, against that probability measure, of `constantTermIntegrand` built from the unipotent family and $f$. (Only the fields `nS` and `ν` of the carrier pins occur; $\Phi_F$, the level subgroups and the Hecke generators enter solely as the remaining fields.) Write $E_f=$ `pseudoEisenstein F f`, so $E_f(g)=f(g)+\sum_{b\in F}^{\prime} f\bigl(w\,u(b)\,g\bigr)$ with $w=$ `adelicWeyl (𝓞 F) F` and $u(b)=$ `unipotentGL2` of the image of $b$ in $\mathbb{A}_F$. Let $\Phi_0=$ `canonicalTruncationDomain F α β`, the third component of `canonicalTruncationData F α β`, i.e. of a choice of datum satisfying `IsTruncationDatum F α β` if one exists and of $((0,0,0,0),\emptyset,\emptyset)$ otherwise; integrals over $\Phi_0$ are taken against the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F`. For $f,h$ put $\langle f,h\rangle=\int_K f(k)\overline{h(k)}\,dk$, the integral over the compact group `adelicMaximalCompact F` against `maximalCompactHaar F`, and let
--   $$Mf(g)=\bigl(\mathrm{adelicAddHaar}(\mathrm{adelicBox}\,F)\bigr)^{-1}\!\!\int_{\mathbb{A}_F} f\bigl(w^{-1}u(x)g\bigr)\,dx$$
--   be `weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)` normalised by the inverse of the real volume of the box. Finally set $X=s+\overline{s'}$ and $Y=s-\overline{s'}$.
--
--   Conclusion. For all real $R,R'$ with $R_0\le R$ and $R\le R'$, the following four statements hold.
--
--   First, the function $g\mapsto \Lambda^{e^{R}}E_\varphi(g)\cdot\overline{\Lambda^{e^{R}}E_\psi(g)}$ is integrable on $\Phi_0$ for `adelicGLHaar (Fin 2) (𝓞 F) F`.
--
--   Second, the function $g\mapsto \Lambda^{e^{R'}}E_\varphi(g)\cdot\overline{\Lambda^{e^{R'}}E_\psi(g)}$ is integrable on $\Phi_0$ for the same measure.
--
--   Third (diagonal case): if $\mu=\nu$ and $s\neq\overline{s'}$, then
--   $$\int_{\Phi_0}\Lambda^{e^{R'}}E_\varphi\,\overline{\Lambda^{e^{R'}}E_\psi}\;-\;\int_{\Phi_0}\Lambda^{e^{R}}E_\varphi\,\overline{\Lambda^{e^{R}}E_\psi}\;=\;c\,\bigl(B_4(R')-B_4(R)\bigr),$$
--   where for a real $\rho$
--   $$B_4(\rho)=\langle\varphi,\psi\rangle\frac{e^{\rho X}}{X}-\langle M\varphi,M\psi\rangle\frac{e^{-\rho X}}{X}+\langle\varphi,M\psi\rangle\frac{e^{\rho Y}}{Y}-\langle M\varphi,\psi\rangle\frac{e^{-\rho Y}}{Y}.$$
--
--   Fourth (off-diagonal case): if there exists $z$ in [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16), the kernel of the distributive Haar character, with $\mu(z)\neq\nu(z)$, then
--   $$\int_{\Phi_0}\Lambda^{e^{R'}}E_\varphi\,\overline{\Lambda^{e^{R'}}E_\psi}\;-\;\int_{\Phi_0}\Lambda^{e^{R}}E_\varphi\,\overline{\Lambda^{e^{R}}E_\psi}\;=\;c\,\bigl(B_2(R')-B_2(R)\bigr),$$
--   where
--   $$B_2(\rho)=\langle\varphi,\psi\rangle\frac{e^{\rho X}}{X}-\langle M\varphi,M\psi\rangle\frac{e^{-\rho X}}{X}.$$
--   The constant $c$ and the threshold $R_0$ are quantified before $\mu,\nu,s,s',\varphi,\psi$ and before $R,R'$, so they are uniform in all of these; the real number $c$ is cast to $\mathbb{C}$ on the right-hand sides. No hypothesis forcing $X\neq 0$ is imposed, the conditions $\operatorname{Re}s,\operatorname{Re}s'>1/2$ giving $\operatorname{Re}X>1$.
--
--   This is the increment form of the Maass–Selberg relations for $\mathrm{GL}_2$ over a number field in the region of absolute convergence: it computes the change, between two truncation heights $e^{R}\le e^{R'}$, of the inner product of truncated pseudo-Eisenstein series over the canonical truncation domain of the determinant slab $(\alpha,\beta)$, in a four-term shape when the two inducing characters agree and in a two-term shape when they differ on some norm-one idele, both with a single constant $c$ and a single threshold $R_0$. It feeds the axis-continuation form of the relations, [`AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_slab_of_ne`](thm.html#AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_slab_of_ne), in the spectral-theoretic input to the analytic theory of automorphic forms on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_slab
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
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
    ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' →
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
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (μ = ν → s ≠ conj s' →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
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
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s')
          + (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s - conj s')) / (s - conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s - conj s'))) / (s - conj s') ) -
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
              Complex.exp (-((R : ℂ) * (s - conj s'))) / (s - conj s') ))) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
      ((∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F φ) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R')
          (AutomorphicForm.pseudoEisenstein F ψ) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
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
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F))) =
      (c : ℂ) *
        (( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R' : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R' : ℂ) * (s + conj s'))) / (s + conj s') ) -
         ( (∫ k, φ (k : AdelicGL2 (𝓞 F) F) * conj (ψ (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (s + conj s')) / (s + conj s')
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (s + conj s'))) / (s + conj s') ))) := by sorry
