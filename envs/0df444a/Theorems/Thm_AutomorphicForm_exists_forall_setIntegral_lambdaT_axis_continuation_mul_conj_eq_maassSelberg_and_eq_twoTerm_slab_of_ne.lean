-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_slab_of_ne
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_slab_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/8a7d5e13-69d3-5e9a-9219-dcf82e3f21a5
-- title:
--   Maass–Selberg relations on the unitary axis at distinct parameters
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A} = \mathbb{A}_F$, let $\alpha,\beta$ be reals with $0 < \alpha$ and $\alpha < \beta$, and let $\Phi_F$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A})$ (the set entering the truncation pins below). Write $\alpha_m \colon \mathbb{A}^\times \to \mathbb{R}^\times$ for the unit-group homomorphism obtained from the module character `distribHaarChar` of $\mathbb{A}$ by composing with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, the adele ring carrying its Borel $\sigma$-algebra, and let $h_{\alpha m}$ be the hypothesis that $\alpha_m(x) > 0$ for every $x$.
--
--   Under these data the assertion is: there exist a real $c > 0$ and a real $R_0$ such that the following holds for all further data, $c$ and $R_0$ being chosen before them.
--
--   The further data are: two homomorphisms $\mu,\nu \colon \mathbb{A}^\times \to \mathbb{C}^\times$; *character hypotheses* on each of them, namely unitarity ($\|\mu(x)\| = 1$ for all $x$, likewise for $\nu$), triviality on the principal ideles (for every $u \in F^\times$, $\mu$ of the image of $u$ is $1$, likewise for $\nu$), and continuity of $x \mapsto \mu(x)$ and $x \mapsto \nu(x)$ as $\mathbb{C}$-valued functions. Next, a family $\varphi \colon \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$, written $\varphi_s$, subject to seven *section hypotheses*: for every $s$, $\varphi_s$ is an induced section for the pair $(\eta_1(s),\eta_2(s)) = (\mu\cdot\alpha_m^{\,s+1/2},\ \nu\cdot\alpha_m^{-(s+1/2)})$, i.e. $\varphi_s(bg) = \eta_1(s)(b_{11})\,\eta_2(s)(b_{22})\,\varphi_s(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (lower-left entry zero); for every $s$, $\varphi_s$ is archimedean $K$-finite, meaning that at each infinite place $w$ the right translates of $\varphi_s$ under the subgroup of $\mathrm{GL}_2(\mathbb{A})$ induced from the row-isometries of $F_w$ span a finite-dimensional space; for every $s$, $\varphi_s$ is $K_f$-smooth, meaning that its stabiliser under right translation by the kernel of the archimedean projection $\mathrm{GL}_2(\mathbb{A}) \to \mathrm{GL}_2(\mathbb{A}_\infty)$ is open; the map $(s,g) \mapsto \varphi_s(g)$ is continuous; for every $g$, $s \mapsto \varphi_s(g)$ is differentiable on $\mathbb{C}$; and a uniform $K$-finiteness clause: at each infinite place $w$ there is a finite-dimensional subspace $W$ of the functions on the row-isometry subgroup at $w$ containing $k \mapsto \varphi_s(gk)$ for all $s$ and all $g$. A second family $\psi \colon \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ is subject to the same seven hypotheses, with the same $\mu,\nu$.
--
--   Then come *axis-continuation data* for each family. For $\varphi$: a set $O_\varphi \subseteq \mathbb{C}$ and functions $E_\varphi, N_\varphi \colon \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$, with a nine-clause hypothesis requiring that $O_\varphi$ be open and preconnected and contain both the imaginary axis $\{\operatorname{Re} s = 0\}$ and the half-plane $\{\operatorname{Re} s > 1/2\}$; that for each $g$ the functions $s \mapsto E_\varphi(s)(g)$ and $s \mapsto N_\varphi(s)(g)$ be analytic on a neighbourhood of every point of $O_\varphi$; that $(s,g) \mapsto E_\varphi(s)(g)$ and $(s,g) \mapsto N_\varphi(s)(g)$ be continuous on $O_\varphi \times \mathrm{GL}_2(\mathbb{A})$; and that on $\operatorname{Re} s > 1/2$ the two functions be given by the Eisenstein expansion and by the intertwining integral, namely $E_\varphi(s)(g) = \varphi_s(g) + \sum_{\xi \in F}' \varphi_s(w\,u(\xi)\,g)$, where $w$ is the adelic Weyl element and $u(\xi)$ the upper unipotent matrix with entry the image of $\xi$ in $\mathbb{A}$, and $N_\varphi(s)(g) = \int \varphi_s(w^{-1} u(x) g)\,dx$ against additive Haar measure on $\mathbb{A}$. The analogous data $O_\psi, E_\psi, N_\psi$ with the same nine clauses is required for $\psi$.
--
--   Finally, reals $t,t'$ with $t \neq t'$, and a real $R$ with $R_0 \le R$.
--
--   For the conclusion, put $s = it$ and $s' = it'$, so that $\overline{s'} = -it'$, $s + \overline{s'} = i(t-t')$ and $s - \overline{s'} = i(t+t')$. Truncation is performed by the operator $\lambda_T$ at level $T = e^{R}$ for the height function $\mathrm{adelicHeight}_F$ (the product of the archimedean height of the archimedean part and the finite height of the finite part): for a function $f$ on $\mathrm{GL}_2(\mathbb{A})$, $(\lambda_T f)(g) = f(g) - \mathbf{1}_{\{h\,:\,T < \mathrm{adelicHeight}_F(h)\}}(g)\cdot \mathrm{constantTerm}(f)(g)$, the constant term being formed with the one-parameter unipotent family $x \mapsto u(x)$ and with the measure supplied by the production pins $\mathrm{productionPinsOf}\,F\,\Phi_F\,(M \mapsto \mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup})\,(v \mapsto \mathrm{heckeGen}(v))\,(\mathrm{adelicBox}\,F)$, i.e. the conditioning of additive Haar measure on $\mathbb{A}$ to the adelic box, with the Borel $\sigma$-algebra on $\mathbb{A}$. Integration of the truncated product is over the canonical truncation domain of $F$ for $(\alpha,\beta)$ — the third component of the canonically chosen truncation datum — against the Haar measure $\mathrm{adelicGLHaar}$ of $\mathrm{GL}_2(\mathbb{A})$. Write $\langle a, b\rangle = \int_{\mathbf{K}} a(k)\,\overline{b(k)}\,dk$ for integration over the adelic maximal compact subgroup $\mathbf{K}$ (matrices integral at all finite places and row-isometric at all infinite places) against its Haar measure, let $q$ be the real volume of the adelic box under additive Haar measure, and set $M_\varphi(s) = q^{-1} N_\varphi(s)$, $M_\psi(s') = q^{-1} N_\psi(s')$.
--
--   The conclusion is the conjunction of two implications.
--
--   First, if $\mu = \nu$ and $t + t' \neq 0$, then the function $x \mapsto (\lambda_{e^R} E_\varphi(s))(x)\cdot \overline{(\lambda_{e^R} E_\psi(s'))(x)}$ is integrable on the canonical truncation domain, and
--   $$\int (\lambda_{e^R} E_\varphi(s))\,\overline{(\lambda_{e^R} E_\psi(s'))} = c\Big(\langle \varphi_s, \psi_{s'}\rangle \frac{e^{R(s+\overline{s'})}}{s+\overline{s'}} - \langle M_\varphi(s), M_\psi(s')\rangle \frac{e^{-R(s+\overline{s'})}}{s+\overline{s'}} + \langle \varphi_s, M_\psi(s')\rangle \frac{e^{R(s-\overline{s'})}}{s-\overline{s'}} - \langle M_\varphi(s), \psi_{s'}\rangle \frac{e^{-R(s-\overline{s'})}}{s-\overline{s'}}\Big),$$
--   with $c$ viewed in $\mathbb{C}$.
--
--   Second, if there exists $z$ in the norm-one ideles of $F$ (the kernel of the module character of $\mathbb{A}$) with $\mu(z) \neq \nu(z)$, then the same product is integrable on the canonical truncation domain, and its integral equals $c$ times the first two terms only,
--   $$c\Big(\langle \varphi_s, \psi_{s'}\rangle \frac{e^{R(s+\overline{s'})}}{s+\overline{s'}} - \langle M_\varphi(s), M_\psi(s')\rangle \frac{e^{-R(s+\overline{s'})}}{s+\overline{s'}}\Big).$$
--   Both implications are asserted with one and the same constant $c$ and threshold $R_0$, uniformly in $(\mu,\nu)$, in the two section families and their continuation data, and in $t,t',R$.
--
--   This is the Maass–Selberg relation for truncated Eisenstein series continued to the unitary axis, in the determinant slab $\alpha < \cdot < \beta$: a four-term relation when the two inducing characters agree and the parameters satisfy $t+t' \neq 0$, and a two-term relation when the characters differ somewhere on the norm-one ideles. It is the common source of the two separate relations [`AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne`](thm.html#AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_slab_of_ne) and [`AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles`](thm.html#AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles), and of their combined form [`AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat`](thm.html#AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat), which feed the analysis of the continuous spectrum for $\mathrm{GL}_2$ over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_slab_of_ne.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_slab_of_ne
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
      (t t' : ℝ) (_ht : t ≠ t') (R : ℝ) (_hR : R₀ ≤ R),
      (μ = ν → t + t' ≠ 0 →
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
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
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
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)) )) := by sorry
