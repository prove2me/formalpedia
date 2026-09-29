-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/0815a61e-ec32-5f69-814e-84638dd2a317
-- title:
--   Two-term Maass–Selberg relation for an off-diagonal pair
-- statement:
--   Throughout, $F$ is a number field, $\alpha,\beta$ are real numbers with $0<\alpha$ and $\alpha<\beta$, and $\Phi_F$ is a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`. The idelic modulus is the character $\alpha_m \colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F)` by composing with the coercion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units, the adele ring carrying its Borel measurable structure `adeleBorel (𝓞 F) F`; the hypothesis $h_{\alpha m}$ states that $\alpha_m(x)>0$ for every idele $x$.
--
--   Under these standing assumptions the assertion is that there exist a real constant $c>0$ and a real number $R_0$, both independent of all the data listed below, such that the following holds for every choice of that data.
--
--   Characters. Two monoid homomorphisms $\mu,\nu\colon \mathbb{A}_F^\times\to\mathbb{C}^\times$ are given, subject to: the off-diagonality hypothesis, that $\mu z \neq \nu z$ for some $z$ in [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16), the kernel of the distributive Haar character; unitarity of $\mu$ and of $\nu$, i.e. $|\mu(x)|=|\nu(x)|=1$ for all $x$; triviality on principal ideles, i.e. $\mu$ and $\nu$ kill the image of $F^\times$ under $\mathrm{Units.map}(\mathrm{algebraMap}\,F\,\mathbb{A}_F)$; and continuity of $x\mapsto \mu(x)$ and $x\mapsto\nu(x)$ as $\mathbb{C}$-valued functions.
--
--   Sections. Two families $\varphi_f,\psi_f\colon \mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ are given, each subject to the same six conditions. For every $s$, $\varphi_f(s)$ is an induced section for the pair `etaFst μ αm hαm s` $=\mu\,|\cdot|^{s+1/2}$ and `etaSnd ν αm hαm s` $=\nu\,|\cdot|^{-(s+1/2)}$ (here $|\cdot|^{w}$ denotes `cpowChar αm hαm w`, $x\mapsto \alpha_m(x)^{w}$), that is, $\varphi_f(s)(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_f(s)(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry), with $\chi_1,\chi_2$ the two characters just described. For every $s$, $\varphi_f(s)$ satisfies `IsArchKFinite F`, i.e. at each infinite place $w$ it satisfies `RightTranslatesSpanFinite` for the subgroup `archRowIsometrySubgroup F w`, the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$. For every $s$, $\varphi_f(s)$ is $K_f$-smooth: its stabiliser, as a right-translation vector, in the kernel `finiteAdelicGL2Subgroup F` of `glArch (𝓞 F) F` is open. The map $(s,g)\mapsto\varphi_f(s)(g)$ is continuous on $\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)$, and $s\mapsto\varphi_f(s)(g)$ is differentiable on all of $\mathbb{C}$ for each $g$. Finally, uniform archimedean $K$-finiteness: for each infinite place $w$ there is a finite-dimensional $\mathbb{C}$-submodule $W$ of functions on `archRowIsometrySubgroup F w` containing $k\mapsto \varphi_f(s)(gk)$ for all $s$ and all $g$. The family $\psi_f$ is subject to the six corresponding conditions, with the same pair of characters.
--
--   Continuation data. A set $O_\varphi\subseteq\mathbb{C}$ and functions $E_\varphi,N_\varphi\colon\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ are given together with a hypothesis of ten conjuncts: $O_\varphi$ is open and preconnected; it contains the unitary axis $\{\operatorname{Re} s=0\}$ and the half-plane $\{\operatorname{Re} s>1/2\}$; for each $g$, both $s\mapsto E_\varphi(s)(g)$ and $s\mapsto N_\varphi(s)(g)$ are analytic on a neighbourhood of each point of $O_\varphi$; both $(s,g)\mapsto E_\varphi(s)(g)$ and $(s,g)\mapsto N_\varphi(s)(g)$ are continuous on $O_\varphi\times\mathrm{GL}_2(\mathbb{A}_F)$; for $\operatorname{Re} s>1/2$ and all $g$, $E_\varphi(s)(g)=\varphi_f(s)(g)+\sum_{\xi\in F}\varphi_f(s)\bigl(w\,n(\xi)\,g\bigr)$, where $w$ is `adelicWeyl (𝓞 F) F` and $n(\xi)$ the unipotent matrix $\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ over $\mathbb{A}_F$; and for $\operatorname{Re} s>1/2$ and all $g$, $N_\varphi(s)(g)=\int_{\mathbb{A}_F}\varphi_f(s)\bigl(w^{-1}n(x)g\bigr)\,dx$ against the additive Haar measure `adelicAddHaar (𝓞 F) F`. A set $O_\psi$ and functions $E_\psi,N_\psi$ are given with the ten corresponding conjuncts relative to $\psi_f$.
--
--   Parameters. Real numbers $t\neq t'$ and a real number $R$ with $R_0\le R$ are given.
--
--   Conclusion. Write $\Lambda^{e^R}$ for the truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48), formed with the measurable structure `nS` and the measure `ν` of the pin data `productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)` — namely the Borel structure on $\mathbb{A}_F$ and the Haar measure `adelicAddHaar (𝓞 F) F` conditioned on the box `adelicBox F` — with the unipotent embedding $x\mapsto n(x)$, the height function [`NumberField.AdelicHeight.adelicHeight F`](def/NumberField_AdelicHeight.html#L158) (the product of the archimedean and finite local heights) and the truncation parameter $e^R$: thus $\Lambda^{e^R}\phi(g)=\phi(g)-\mathbf{1}_{\{h:\ e^R<\mathrm{adelicHeight}(h)\}}(g)\cdot\int n\text{-constant term of }\phi\text{ at }g$. Then, with $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain F α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) (the second set component of the canonical truncation datum for $\alpha,\beta$) and with the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` on $\mathrm{GL}_2(\mathbb{A}_F)$, two assertions hold.
--
--   First, the function
--   $$x\longmapsto \Lambda^{e^R}\bigl(E_\varphi(it)\bigr)(x)\cdot\overline{\Lambda^{e^R}\bigl(E_\psi(it')\bigr)(x)}$$
--   is integrable on $\Phi_0$ with respect to `adelicGLHaar (Fin 2) (𝓞 F) F`.
--
--   Second, its integral over $\Phi_0$ equals
--   $$c\left(\frac{\langle \varphi_f(it),\psi_f(it')\rangle\,e^{R(it+\overline{it'})}}{it+\overline{it'}}\;-\;\frac{\langle \mathrm{vol}^{-1}N_\varphi(it),\ \mathrm{vol}^{-1}N_\psi(it')\rangle\,e^{-R(it+\overline{it'})}}{it+\overline{it'}}\right),$$
--   where $\langle a,b\rangle=\int_{\mathbf{K}}a(k)\overline{b(k)}\,dk$ is taken over the maximal compact subgroup `adelicMaximalCompact F` against [`AutomorphicForm.maximalCompactHaar F`](def/AutomorphicForm_AdelicMaximalCompact.html#L208), the arguments of $\langle\cdot,\cdot\rangle$ being restricted to $\mathbf{K}$, and $\mathrm{vol}=\bigl(\mathrm{adelicAddHaar}\,(\mathcal{O}_F)\,F\bigr)\bigl(\mathrm{adelicBox}\,F\bigr)$ in its real-to-complex form, so that $\mathrm{vol}^{-1}N$ is the normalised intertwining function. Since $it+\overline{it'}=i(t-t')$ and $t\neq t'$, the denominators are non-zero; only the two terms of frequency $\pm(t-t')$ occur, the cross terms of frequency $\pm(t+t')$ being absent.
--
--   This is the Maass–Selberg relation on the unitary axis for truncated Eisenstein series attached to an off-diagonal pair of unitary idele class characters, evaluated at two distinct purely imaginary parameters $it\neq it'$: for such a pair the inner product of the truncated series reduces to the two terms of frequency $\pm(t-t')$, in contrast with the four-term bracket obtained for a diagonal pair. It is used to derive the unitarity of the normalised intertwining operator on the axis, in [`AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar`](thm.html#AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_twoTerm_slab_of_ne_of_exists_normOneIdeles
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
      (_hμν : ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z)
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
              Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)) ) := by sorry
