-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
-- name    : AutomorphicForm.exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/4f7cbd6e-91bb-598f-89f8-8e3aaebebb58
-- title:
--   Uniform L² bound for truncated unitary Eisenstein series
-- statement:
--   Let $F$ be a number field, let $0<\alpha<\beta$ be reals, let $\Phi_F$ be a set of adelic $GL_2$-points and let $\mathfrak N$ be a nonzero ideal of $\mathcal O_F$. Write $\alpha_m$ for the character of the idele group obtained from the module character `distribHaarChar` of the adele ring, viewed in $\mathbb R^\times$, and assume it is everywhere positive. Then there are $c>0$ and $R_0\in\mathbb R$, depending only on these data, such that the following holds for all characters $\mu,\nu$ of the idele group with values in $\mathbb C^\times$ which are continuous, of absolute value $1$ everywhere, trivial on the principal ideles $F^\times$, and satisfy either $\mu=\nu$ or $\mu z\neq\nu z$ for some $z$ in the kernel of `distribHaarChar`; for all families $\varphi:\mathbb C\times GL_2(\mathbb A_F)\to\mathbb C$ such that each $\varphi_s$ satisfies $\varphi_s(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel subgroup, with $\eta_1=\mu\cdot\alpha_m^{s+1/2}$ and $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$, such that at each infinite place $w$ the right translates of $\varphi_s$ under the row-isometry subgroup at $w$ span a finite-dimensional space, the stabiliser of $\varphi_s$ in the finite-adelic subgroup is open, $(s,g)\mapsto\varphi_s(g)$ is continuous, $s\mapsto\varphi_s(g)$ is entire, for each $w$ there is one finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing all the restricted right translates of all $\varphi_s$, $\varphi_s$ agrees with $\varphi_0$ on the adelic maximal compact subgroup, and $\varphi_s$ is right invariant under the intersection of the principal level subgroup at $\mathfrak N$ with the finite-adelic subgroup; and for all $O_\varphi\subseteq\mathbb C$ open and preconnected containing both $\{\operatorname{Re}s=0\}$ and $\{\operatorname{Re}s>1/2\}$ and all $E_\varphi,N_\varphi$ which are analytic in $s$ on $O_\varphi$ for each $g$, jointly continuous on $O_\varphi\times GL_2(\mathbb A_F)$, and satisfy, for $\operatorname{Re}s>1/2$, $E_\varphi(s,g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w\,n(\xi)g)$ with $w$ the adelic Weyl element and $n$ the upper unipotent, and $N_\varphi(s,g)=\int\varphi_s(w^{-1}n(x)g)\,dx$ against additive adelic Haar measure. Namely, for every real $t\neq0$, every $R\geq R_0$ and all $B_1,B_2\geq0$ such that the $L^2$-norm over the adelic maximal compact subgroup $\mathbf K$ (with its Haar measure) of $k\mapsto\operatorname{vol}(\mathrm{box})^{-1}\,\partial_s N_\varphi(s,k)|_{s=it}$ is at most $B_1$, where $\operatorname{vol}(\mathrm{box})$ is the additive adelic Haar volume of the adelic box, and such that for all real $s$ with $|s|\le1$ the difference of the pairings $\int_{\mathbf K}\varphi_{is}(k)\overline{\operatorname{vol}(\mathrm{box})^{-1}N_\varphi(is,k)}\,dk$ and $\int_{\mathbf K}\varphi_0(k)\overline{\operatorname{vol}(\mathrm{box})^{-1}N_\varphi(0,k)}\,dk$ has norm at most $B_2|s|$: the function $x\mapsto\|\Lambda^{e^R}E_\varphi(it,\cdot)(x)\|^2$ is integrable on the canonical truncation domain attached to $(\alpha,\beta)$ against adelic Haar measure on $GL_2$, and its integral there is at most $c\bigl((|R|+1)P+\sqrt P\,B_1+B_2\bigr)$, where $P=\int_{\mathbf K}\|\varphi_0(k)\|^2dk$. Here $\Lambda^{e^R}$ is the truncation that subtracts, at points of adelic height exceeding $e^R$, the constant term $g\mapsto\int\,E_\varphi(it,n(q)g)\,d\nu(q)$ along the upper unipotent, $\nu$ being the additive adelic Haar measure conditioned on the adelic box, these measure data being read off from the pins record built from $\Phi_F$, the principal level subgroups intersected with the finite-adelic subgroup, the local Hecke generators and the adelic box.
--
--   This is the Maass–Selberg $L^2$ estimate for truncated Eisenstein series on $GL_2$ over a number field, specialised to the unitary axis $s=it$ and made uniform in the spectral parameter and in the inducing data, all terms on the right being pairings over the maximal compact subgroup. It feeds the subsequent bound in which the dependence on the level and on the spectral parameter is turned into an explicit power, en route to the spectral estimates used for the adelic trace-formula input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F))
    (𝔑 : Ideal (𝓞 F)) (_h𝔑 : 𝔑 ≠ ⊥) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hpair : μ = ν ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z)
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        φf s (k : AdelicGL2 (𝓞 F) F) = φf 0 (k : AdelicGL2 (𝓞 F) F))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F 𝔑 ⊓ finiteAdelicGL2Subgroup F, φf s (g * u) = φf s g)
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
      (t : ℝ) (_ht : t ≠ 0) (R : ℝ) (_hR : R₀ ≤ R)
      (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
      (_hderiv : eLpNorm (fun k : adelicMaximalCompact F =>
          ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
            deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I))
        2 (AutomorphicForm.maximalCompactHaar F) ≤ ENNReal.ofReal B₁)
      (_hlip : ∀ s : ℝ, |s| ≤ 1 →
        ‖(∫ k, φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
              conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((s : ℂ) * Complex.I) g)
                (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)) -
          (∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
              conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ 0 g)
                (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F))‖ ≤ B₂ * |s|),
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I)) x‖ ^ 2)
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I)) x‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤
        c * ((|R| + 1) * (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F)) +
          Real.sqrt (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F)) * B₁ + B₂) := by sorry
