-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/96389c71-b0f1-583e-b527-028d8dc94bdb
-- title:
--   Maass–Selberg relations on the unitary axis, two character pairs
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_F$ be a subset of $\mathrm{GL}_2$ of the adele ring of $F$. Write $\alpha_m$ for the homomorphism from the idele group to $\mathbb{R}^\times$ obtained from `distribHaarChar` of the adele ring by pushing $\mathbb{R}_{\ge 0}$ into $\mathbb{R}$ and passing to units, and assume the hypothesis $h_{\alpha m}$: $\alpha_m(x)>0$ for every idele $x$. The adeles carry their Borel $\sigma$-algebra and $\mathrm{GL}_2$ of the adeles its Borel $\sigma$-algebra with Haar measure `adelicGLHaar`.
--
--   Under these data the assertion is the existence of a real $c>0$ and of a real $R_0$ — both chosen before, hence uniformly in, all the remaining data — such that the following holds for all quadruples of characters, all families of sections, all analytic continuations and all parameters as listed below.
--
--   Character hypotheses. $\mu,\nu,\mu',\nu'$ are homomorphisms from the idele group to $\mathbb{C}^\times$; the four hypotheses `IsUnitaryChar` state that each has absolute value $1$ at every idele, the four hypotheses `IsIdeleClassChar` state that each is trivial on the image of $F^\times$ in the ideles, and four further hypotheses state that each is continuous as a $\mathbb{C}$-valued function on the ideles.
--
--   Section families. $\varphi_f:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfies: for every $s$, $\varphi_f(s)$ is an induced section for the pair $(\mu\cdot\alpha_m^{\,s+1/2},\ \nu\cdot\alpha_m^{-(s+1/2)})$, i.e. $\varphi_f(s)(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_f(s)(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero) and all $g$, with $\chi_1,\chi_2$ the two characters just named; for every $s$, $\varphi_f(s)$ is `IsArchKFinite`, i.e. at each infinite place $w$ its right translates under the image of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$ span a finite-dimensional space; for every $s$, $\varphi_f(s)$ is `IsKfSmooth`, i.e. its stabiliser for right translation inside the subgroup of adelic matrices with trivial archimedean component is open; the map $(s,g)\mapsto\varphi_f(s)(g)$ is continuous; for every $g$ the function $s\mapsto\varphi_f(s)(g)$ is differentiable on $\mathbb{C}$; and a uniform $K$-finiteness hypothesis: for each infinite place $w$ there is a finite-dimensional $\mathbb{C}$-submodule $W$ of functions on the archimedean row-isometry subgroup at $w$ containing, for all $s$ and $g$, the function $k\mapsto\varphi_f(s)(gk)$. The family $\psi_f$ satisfies exactly the same six hypotheses with $(\mu,\nu)$ replaced by $(\mu',\nu')$.
--
--   Continuation packages. $O_\varphi\subseteq\mathbb{C}$ and $E_\varphi,N_\varphi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ are subject to a nine-clause hypothesis: $O_\varphi$ is open and preconnected, contains the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_\varphi(s)(g)$ and $s\mapsto N_\varphi(s)(g)$ are analytic on a neighbourhood of each point of $O_\varphi$; both $(s,g)\mapsto E_\varphi(s)(g)$ and $(s,g)\mapsto N_\varphi(s)(g)$ are continuous on $O_\varphi\times\mathrm{univ}$; for $\mathrm{Re}\,s>1/2$ and all $g$, $E_\varphi(s)(g)=\varphi_f(s)(g)+\sum_{\xi\in F}\varphi_f(s)\bigl(w\,n(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $n(\xi)$ the upper unipotent matrix with entry the image of $\xi$; and for $\mathrm{Re}\,s>1/2$ and all $g$, $N_\varphi(s)(g)=\int_{\mathbb{A}_F}\varphi_f(s)\bigl(w^{-1}n(x)g\bigr)\,dx$ against the additive adelic Haar measure. The triple $(O_\psi,E_\psi,N_\psi)$ is subject to the same nine clauses with $\psi_f$ in place of $\varphi_f$.
--
--   Parameters. $t,t'$ are reals with $t\neq t'$, and $R$ is a real with $R_0\le R$.
--
--   Notation for the conclusion. For a function $X$ on $\mathrm{GL}_2(\mathbb{A}_F)$ write $\Lambda^R X$ for `lambdaT` formed with the measurable space and measure supplied by the record `productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)` — only its fields `nS` (the Borel $\sigma$-algebra of the adeles) and `ν` (the additive adelic Haar measure conditioned on `adelicBox F`) are used — with unipotent family $q\mapsto$ `unipotentGL2` $q$, height function `adelicHeight F` and threshold $e^{R}$; thus $\Lambda^R X(g)=X(g)-\mathbf 1_{\{\,e^{R}<\mathrm{adelicHeight}(g)\,\}}(g)\cdot \mathrm{constantTerm}(X)(g)$, the constant term being the integral of the `constantTerm` integrand over the conditioned measure. Set $s=it$ and $s'=it'$. Integration in $x$ is over `canonicalTruncationDomain F α β` (the third component of `canonicalTruncationData F α β`, a chosen truncation datum for $(\alpha,\beta)$ when one exists and $\emptyset$ otherwise) against `adelicGLHaar`. Integration in $k$ is over the adelic maximal compact subgroup against `maximalCompactHaar F`. Write $M_\varphi(s)=\operatorname{vol}(\mathrm{box})^{-1}N_\varphi(s)$ and $M_\psi(s')=\operatorname{vol}(\mathrm{box})^{-1}N_\psi(s')$, where $\operatorname{vol}(\mathrm{box})$ is the real number attached to `adelicBox F` by the additive adelic Haar measure, and put
--   $$A=\Bigl(\int_k \varphi_f(s)(k)\overline{\psi_f(s')(k)}\Bigr)\frac{e^{R(s+\bar s')}}{s+\bar s'},\quad B=\Bigl(\int_k M_\varphi(s)(k)\overline{M_\psi(s')(k)}\Bigr)\frac{e^{-R(s+\bar s')}}{s+\bar s'},$$
--   $$C=\Bigl(\int_k \varphi_f(s)(k)\overline{M_\psi(s')(k)}\Bigr)\frac{e^{R(s-\bar s')}}{s-\bar s'},\quad D=\Bigl(\int_k M_\varphi(s)(k)\overline{\psi_f(s')(k)}\Bigr)\frac{e^{-R(s-\bar s')}}{s-\bar s'}.$$
--
--   The conclusion is a conjunction of four implications concerning the function $x\mapsto \Lambda^R\bigl(E_\varphi(s)\bigr)(x)\cdot\overline{\Lambda^R\bigl(E_\psi(s')\bigr)(x)}$ on the canonical truncation domain.
--
--   First, if $\mu'=\mu$, $\nu'=\nu$, $\mu=\nu$ and $t+t'\neq 0$, then that function is integrable on the canonical truncation domain and its integral equals $c\,(A-B+C-D)$.
--
--   Second, if $\mu'=\mu$, $\nu'=\nu$ and there is an idele $z$ in the kernel of `distribHaarChar` (the norm-one ideles) with $\mu(z)\neq\nu(z)$, then the function is integrable on the canonical truncation domain and its integral equals $c\,(A-B)$; no condition on $t+t'$ is imposed here.
--
--   Third, if $\mu'=\nu$, $\nu'=\mu$, there is a norm-one idele $z$ with $\mu(z)\neq\nu(z)$, and $t+t'\neq 0$, then the function is integrable on the canonical truncation domain and its integral equals $c\,(C-D)$.
--
--   Fourth, if there is a norm-one idele $z$ with $\mu'(z)\neq\mu(z)$ or $\nu'(z)\neq\nu(z)$, and there is a norm-one idele $z$ with $\mu'(z)\neq\nu(z)$ or $\nu'(z)\neq\mu(z)$, then the function is integrable on the canonical truncation domain and its integral is $0$.
--
--   This is the Maass–Selberg inner product formula for truncated $\mathrm{GL}_2$ Eisenstein series over a number field, evaluated at two distinct points $it\neq it'$ of the unitary axis and for two possibly different inducing pairs of unitary Hecke characters, in the determinant-slab normalisation; the force of the formulation is that a single constant $c$ and a single threshold $R_0$ serve all four cases (four-term, two-term, cross and orthogonal) simultaneously. It feeds the statement [`AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat`](thm.html#AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat), within the spectral analysis of the adelic $\mathrm{GL}_2$ continuous spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
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
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hμ'k : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ' x : ℂˣ) : ℂ))
      (_hν'k : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν' x : ℂˣ) : ℂ))
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
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (ψf s))
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
      (t t' : ℝ) (_ht : t ≠ t') (R : ℝ) (_hR : R₀ ≤ R),
      (μ' = μ → ν' = ν → μ = ν → t + t' ≠ 0 →
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
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)) )) ∧
      (μ' = μ → ν' = ν → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
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
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)) )) ∧
      (μ' = ν → ν' = μ → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) → t + t' ≠ 0 →
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
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)) )) ∧
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
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = 0) := by sorry
