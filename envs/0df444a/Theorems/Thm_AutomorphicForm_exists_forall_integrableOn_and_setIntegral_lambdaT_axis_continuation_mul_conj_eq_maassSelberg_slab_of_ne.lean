-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ae76f19e-feb0-5f3e-84c1-73923eb4877e
-- title:
--   Maass–Selberg relation on the unitary axis, diagonal case μ=ν
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}=\mathbb{A}_F$ and $\mathrm{GL}_2(\mathbb{A})$ written `AdelicGL2 (𝓞 F) F`. Let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_F$ be a subset of $\mathrm{GL}_2(\mathbb{A})$. The idelic modulus is the character $\alpha_m\colon \mathbb{A}^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F)` of the adele ring by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units; the adele ring carries its Borel structure `adeleBorel`, and $\mathrm{GL}_2(\mathbb{A})$ the Borel structure `glBorel`. Under the hypothesis $h\alpha_m$ that $\alpha_m(x)>0$ for every idele $x$, the assertion is the existence of a constant $c>0$ and of a threshold $R_0\in\mathbb{R}$, both chosen before all the data that follow, such that the following holds.
--
--   Let $\mu,\nu\colon\mathbb{A}^\times\to\mathbb{C}^\times$ be characters subject to: $\mu=\nu$ (so the statement is the diagonal case only); $\mu$ and $\nu$ unitary, i.e. $\lVert\mu(x)\rVert=\lVert\nu(x)\rVert=1$ for all $x$; $\mu$ and $\nu$ trivial on the principal ideles, i.e. $\mu(u)=\nu(u)=1$ for every $u\in F^\times$ embedded diagonally; and $x\mapsto\mu(x)$, $x\mapsto\nu(x)$ continuous as $\mathbb{C}$-valued functions.
--
--   Let $\varphi\colon\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ be a family of sections satisfying six hypotheses: for every $s$, $\varphi_s$ is an induced section for the pair $(\mathrm{etaFst},\mathrm{etaSnd})=(\mu\,\alpha_m^{\,s+1/2},\ \nu\,\alpha_m^{-(s+1/2)})$, meaning $\varphi_s(bg)=\mu(b_{00})\alpha_m(b_{00})^{s+1/2}\,\nu(b_{11})\alpha_m(b_{11})^{-(s+1/2)}\,\varphi_s(g)$ for every $b$ in the adelic Borel subgroup (lower-left entry zero) and every $g$, where $b_{00},b_{11}$ are the diagonal units of $b$; for every $s$, $\varphi_s$ is archimedean $K$-finite, i.e. satisfies `RightTranslatesSpanFinite` with respect to `archRowIsometrySubgroup F w` — the image in $\mathrm{GL}_2(\mathbb{A})$ of the subgroup of row-isometries of $\mathrm{GL}_2(F_w)$ — at every infinite place $w$; for every $s$, $\varphi_s$ is $K_f$-smooth, i.e. its stabiliser as a right-translation vector in `finiteAdelicGL2Subgroup F` $=\ker(\mathrm{glArch})$ is open; the map $(s,g)\mapsto\varphi_s(g)$ is continuous; for every $g$ the map $s\mapsto\varphi_s(g)$ is differentiable on $\mathbb{C}$; and uniform archimedean $K$-finiteness holds, namely for each infinite place $w$ there is a finite-dimensional $\mathbb{C}$-subspace $W$ of functions on `archRowIsometrySubgroup F w` containing $k\mapsto\varphi_s(gk)$ for all $s$ and all $g$. Let $\psi\colon\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ satisfy the same six hypotheses, with the same pair of characters $(\mu\,\alpha_m^{\,s+1/2},\nu\,\alpha_m^{-(s+1/2)})$.
--
--   Let $O_\varphi\subseteq\mathbb{C}$ and $E_\varphi,N_\varphi\colon\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ satisfy the nine-clause hypothesis of analytic continuation: $O_\varphi$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for every $g$, $s\mapsto E_\varphi(s)(g)$ and $s\mapsto N_\varphi(s)(g)$ are analytic on a neighbourhood of each point of $O_\varphi$; $(s,g)\mapsto E_\varphi(s)(g)$ and $(s,g)\mapsto N_\varphi(s)(g)$ are continuous on $O_\varphi\times\mathrm{GL}_2(\mathbb{A})$; and for $\operatorname{Re}s>1/2$ and all $g$ one has the Bruhat-cell Eisenstein expansion $E_\varphi(s)(g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s\big(w\,n(\xi)\,g\big)$, with $w=$ `adelicWeyl` and $n(\xi)$ the unipotent matrix with upper-right entry the image of $\xi$ in $\mathbb{A}$, together with $N_\varphi(s)(g)=\int_{\mathbb{A}}\varphi_s\big(w^{-1}n(x)g\big)\,dx$, the Weyl intertwining integral against the additive Haar measure `adelicAddHaar`. Let $O_\psi$, $E_\psi$, $N_\psi$ satisfy the same nine clauses for the family $\psi$.
--
--   Finally let $t,t'\in\mathbb{R}$ with $t\neq t'$ and $t+t'\neq 0$, and let $R\in\mathbb{R}$ with $R_0\le R$.
--
--   The truncation operator used is `lambdaT` at height $e^{R}$: for a function $f$ on $\mathrm{GL}_2(\mathbb{A})$,
--   $$\Lambda^{e^R}f(g)=f(g)-\mathbf{1}_{\{g\,:\,e^{R}<H(g)\}}(g)\int f(n(q)g)\,d\nu_0(q),$$
--   where $H=$ `adelicHeight F` is the product of the archimedean height of the archimedean part and the finite height of the finite part, $n$ is `unipotentGL2`, and the measurable structure and measure are the fields `nS` and `ν` of `productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`, that is the Borel structure on $\mathbb{A}$ and the Haar measure `adelicAddHaar` conditioned on the adelic box `adelicBox F`; the set $\Phi_F$, the level subgroups and the Hecke generators occur only as the remaining fields of that record, which the truncation does not read.
--
--   The conclusion is a conjunction of two assertions about the product $\big(\Lambda^{e^R}E_\varphi(it)\big)\cdot\overline{\big(\Lambda^{e^R}E_\psi(it')\big)}$ on the canonical truncation domain `canonicalTruncationDomain F α β` — the third component of the datum selected by `canonicalTruncationData F α β`, a choice of a set satisfying `IsTruncationDatum F α β` if one exists and the empty set otherwise — with respect to the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` on $\mathrm{GL}_2(\mathbb{A})$.
--
--   First, this product is integrable on the canonical truncation domain for that Haar measure.
--
--   Second, writing $\langle a,b\rangle=\int a(k)\,\overline{b(k)}\,dk$ for the integral over the adelic maximal compact subgroup against `maximalCompactHaar F`, and $M_\varphi(s)=V^{-1}N_\varphi(s)$, $M_\psi(s)=V^{-1}N_\psi(s)$ with $V$ the real volume `(adelicAddHaar (𝓞 F) F (adelicBox F)).toReal` of the adelic box viewed in $\mathbb{C}$, the integral equals $c$ (coerced to $\mathbb{C}$) times the four-term bracket
--   $$\langle\varphi_{it},\psi_{it'}\rangle\frac{e^{R(it+\overline{it'})}}{it+\overline{it'}}-\langle M_\varphi(it),M_\psi(it')\rangle\frac{e^{-R(it+\overline{it'})}}{it+\overline{it'}}+\langle\varphi_{it},M_\psi(it')\rangle\frac{e^{R(it-\overline{it'})}}{it-\overline{it'}}-\langle M_\varphi(it),\psi_{it'}\rangle\frac{e^{-R(it-\overline{it'})}}{it-\overline{it'}},$$
--   all four integrals being taken over the adelic maximal compact subgroup against `maximalCompactHaar F`. Here $it+\overline{it'}=i(t-t')$ and $it-\overline{it'}=i(t+t')$, which are non-zero by the hypotheses $t\neq t'$ and $t+t'\neq 0$, so the four denominators do not vanish.
--
--   This is the Maass–Selberg relation for the inner product of two truncated Eisenstein series on $\mathrm{GL}_2$ over a number field, read on the unitary axis at the parameters $s=it$, $s'=it'$ for the analytically continued Eisenstein series and intertwining integrals, in the diagonal case $\mu=\nu$; the four-term bracket is the same as on the slab of absolute convergence. It is obtained by specialising a version that also records a two-term form, and it feeds the identity [`AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar`](thm.html#AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar), the step expressing that the intertwining operator preserves the $\mathbf{K}$-inner product on the unitary axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne
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
      (t t' : ℝ) (_ht : t ≠ t') (_htt' : t + t' ≠ 0) (R : ℝ) (_hR : R₀ ≤ R),
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I)) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eψ ((t' : ℂ) * Complex.I)) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I)) x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eψ ((t' : ℂ) * Complex.I)) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (c : ℂ) *
        ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))
          + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)) ) := by sorry
