-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_axis_continuation_mul_conj_lambdaT_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_forall_integrableOn_axis_continuation_mul_conj_lambdaT_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2a35a2d9-adb6-513a-81e2-7d2548d340fe
-- title:
--   Integrability of truncated axis-continued Eisenstein products on Φ₀
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_F$ be a set of adelic $GL_2$ matrices. Write $\alpha_m$ for the character of $\mathbb{A}_F^\times$ obtained from the distributive Haar character of the adele ring composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, viewed as a homomorphism to $\mathbb{R}^\times$. The assertion is that there exists a real $R_1$ such that the following holds for all data: positivity of $\alpha_m$; characters $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ that are unitary ($\|\chi(x)\|=1$ for all $x$), trivial on the image of $F^\times$, and continuous; families $\varphi_f,\psi_f:\mathbb{C}\times GL_2(\mathbb{A}_F)\to\mathbb{C}$ such that for every $s$ the function $\varphi_f(s,\cdot)$ (and likewise $\psi_f$) transforms under the adelic Borel subgroup by $b g\mapsto \eta_1(b_{11})\eta_2(b_{22})$ times its value, with $\eta_1=\mu\cdot\alpha_m^{\,s+1/2}$ and $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$, which are archimedean $K$-finite (at each infinite place the right translates under the row-isometry subgroup span a finite-dimensional space) and $K_f$-smooth (open stabiliser in the finite adelic subgroup), jointly continuous in $(s,g)$, holomorphic in $s$ for each $g$, and such that for each infinite place $w$ a single finite-dimensional space of functions on the row-isometry subgroup at $w$ contains all restrictions $k\mapsto \varphi_f(s,gk)$, uniformly in $s$ and $g$; and continuation data $(O_\varphi,E_\varphi,N_\varphi)$ and $(O_\psi,E_\psi,N_\psi)$, where $O$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re} s=0\}$ and the half-plane $\{\operatorname{Re} s>1/2\}$, $E$ and $N$ are analytic on a neighbourhood of each point of $O$ in $s$ for every $g$ and jointly continuous on $O\times GL_2(\mathbb{A}_F)$, and on $\{\operatorname{Re} s>1/2\}$ one has $E_s(g)=\varphi_f(s,g)+\sum_{\xi\in F}\varphi_f(s,w\,u(\xi)g)$ with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent, and $N_s(g)=\int \varphi_f(s,w^{-1}u(x)g)\,dx$ against adelic additive Haar measure (and the same for $\psi$). Then for all reals $t$ and $R$ with $R_1\le R$, both $x\mapsto E_\varphi(it)(x)\,\overline{(\Lambda^{e^R}E_\psi(it))(x)}$ and $x\mapsto (\Lambda^{e^R}E_\varphi(it))(x)\,\overline{(\Lambda^{e^R}E_\psi(it))(x)}$ are integrable on $\mathrm{canonicalTruncationDomain}\ F\ \alpha\ \beta$ with respect to the adelic Haar measure on $GL_2(\mathbb{A}_F)$; here $\Lambda^{T}f=f-\mathbf{1}_{\{g\,:\,T<\mathrm{adelicHeight}\,g\}}\cdot(\text{constant term of }f\text{ along }x\mapsto u(x))$, the constant term being taken against the additive adelic Haar measure conditioned on the adelic box, these being the two fields of `productionPinsOf` that the statement uses.
--
--   This is the integrability input (moderate growth of a unitary Eisenstein series against the rapid decay of a truncated one on the canonical truncation domain of the norm slab $[\alpha,\beta]$) needed to manipulate inner products of Eisenstein series on the unitary axis. It is used in the term-by-term evaluation of truncated inner integrals that leads to the identity [`AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation), with the truncation threshold uniform: $R_1$ depends only on $F$ and the slab, being quantified before all the spectral data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_axis_continuation_mul_conj_lambdaT_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TruncationOperator
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

theorem AutomorphicForm.exists_forall_integrableOn_axis_continuation_mul_conj_lambdaT_canonicalTruncationDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∃ R₁ : ℝ,
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      (t R : ℝ), R₁ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F => Eφ ((t : ℂ) * Complex.I) x *
          conj ((@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F => (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))) x *
          conj ((@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
