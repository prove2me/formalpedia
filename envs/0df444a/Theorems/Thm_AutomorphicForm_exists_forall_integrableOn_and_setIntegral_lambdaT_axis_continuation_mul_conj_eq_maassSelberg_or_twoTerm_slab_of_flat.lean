-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/4318d4f6-518c-5382-ab94-e6842ee7a488
-- title:
--   Maass–Selberg relation on the unitary axis, flat families
-- statement:
--   Throughout, $F$ is a number field with ring of integers $\mathcal O_F$ and adele ring $\mathbb A =$ `AdeleRing (𝓞 F) F`, and `AdelicGL2 (𝓞 F) F` is $\mathrm{GL}_2(\mathbb A)$. The data fixed at the outset are two reals $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$, and a set $\Phi_F \subseteq \mathrm{GL}_2(\mathbb A)$. The character $\alpha_m : \mathbb A^\times \to \mathbb R^\times$ is the module character `distribHaarChar (AdeleRing (𝓞 F) F)` of the adele ring, pushed from $\mathbb R_{\ge 0}$ to $\mathbb R$ and viewed as a homomorphism into $\mathbb R^\times$; the adele ring carries its Borel $\sigma$-algebra `adeleBorel`. A hypothesis `hαm` asserts that $\alpha_m$ takes strictly positive real values.
--
--   The assertion is: there exist a real $c > 0$ and a real $R_0$ — both depending only on $F$, $\alpha$, $\beta$, $\Phi_F$ and the measures involved, since they are produced before the remaining data is quantified — such that the following holds for all the data listed next.
--
--   Character data: two monoid homomorphisms $\mu, \nu : \mathbb A^\times \to \mathbb C^\times$, each unitary in the sense of `IsUnitaryChar` (all values of absolute value $1$), each trivial on the image of $F^\times$ in the sense of `IsIdeleClassChar`, and each continuous as a $\mathbb C$-valued function on $\mathbb A^\times$.
--
--   Section data: two families $\varphi : \mathbb C \to \mathrm{GL}_2(\mathbb A) \to \mathbb C$ (written `φf`) and $\psi$ (written `ψf`), each subject to seven hypotheses. For $\varphi$ these are: for every $s$, $\varphi_s$ is an induced section for the pair `etaFst μ αm hαm s` $= \mu\,\alpha_m^{\,s+1/2}$ and `etaSnd ν αm hαm s` $= \nu\,\alpha_m^{-(s+1/2)}$, i.e. $\varphi_s(bg) = \eta_1(b_{11})\,\eta_2(b_{22})\,\varphi_s(g)$ for every $b$ in the Borel subgroup of matrices with vanishing $(1,0)$ entry; for every $s$, $\varphi_s$ is archimedean $K$-finite, meaning that at each infinite place $w$ the right translates of $\varphi_s$ under `archRowIsometrySubgroup F w` (the image in $\mathrm{GL}_2(\mathbb A)$ of the group of row isometries of $\mathrm{GL}_2(F_w)$) span a finite-dimensional space; for every $s$, $\varphi_s$ is $K_f$-smooth, meaning that its stabiliser for right translation inside `finiteAdelicGL2Subgroup F` (the kernel of the archimedean projection `glArch`) is open; the map $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; $s \mapsto \varphi_s(g)$ is entire for each $g$; uniformly in $s$ and $g$ there is, for each infinite place $w$, one finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup F w` containing every function $k \mapsto \varphi_s(gk)$; and finally the flatness hypothesis `_hφflat`: for every $s$ and every $k$ in `adelicMaximalCompact F` (finite part in `finiteIntegralGL2`, every archimedean component a row isometry) one has $\varphi_s(k) = \varphi_0(k)$. The family $\psi$ is subject to the same seven hypotheses, with the same pair of characters $\mu, \nu$.
--
--   Continuation data: a set $O_\varphi \subseteq \mathbb C$ and functions $E_\varphi, N_\varphi : \mathbb C \to \mathrm{GL}_2(\mathbb A) \to \mathbb C$ together with a nine-clause hypothesis `_hEφ`, namely: $O_\varphi$ is open and preconnected, contains the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ the functions $s \mapsto E_\varphi(s,g)$ and $s \mapsto N_\varphi(s,g)$ are analytic on a neighbourhood of each point of $O_\varphi$; $(s,g) \mapsto E_\varphi(s,g)$ and $(s,g) \mapsto N_\varphi(s,g)$ are continuous on $O_\varphi \times \mathrm{GL}_2(\mathbb A)$; for $\mathrm{Re}\,s > 1/2$ and all $g$, $E_\varphi(s,g) = \varphi_s(g) + \sum_{\xi \in F}^{\prime} \varphi_s(w\,u(\xi)\,g)$, where $w =$ `adelicWeyl` is the image of $\begin{pmatrix} 0&1\\1&0\end{pmatrix}$ and $u(\xi)$ is the unipotent matrix with upper right entry the image of $\xi$; and for $\mathrm{Re}\,s > 1/2$ and all $g$, $N_\varphi(s,g) = \int_{\mathbb A} \varphi_s(w^{-1} u(x) g)\,dx$ with respect to `adelicAddHaar`. The analogous set $O_\psi$, functions $E_\psi, N_\psi$ and nine-clause hypothesis `_hEψ` are imposed for $\psi$.
--
--   Finally, a real $t$ with $t \neq 0$ and a real $R$ with $R_0 \le R$.
--
--   Two abbreviations are used below. First, $\Lambda^{e^R}$ denotes the truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with the data packaged by `productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`, of which only the measurable space `adeleBorel` and the measure $\nu =$ `ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)`, the normalised restriction of additive adelic Haar measure to the box `adelicBox F`, enter; with the unipotent family $x \mapsto$ `unipotentGL2 x`, the height function [`NumberField.AdelicHeight.adelicHeight F`](def/NumberField_AdelicHeight.html#L158) and the threshold $e^R$, it sends $f$ to $f - \mathbf 1_{\{g\,:\,e^R < \mathrm{ht}(g)\}}\cdot(\text{constant term of } f)$, the constant term being the integral of `constantTermIntegrand` along the unipotent family against that normalised measure. Second, $\langle a, b\rangle := \int_{\mathbf K} a(k)\,\overline{b(k)}\,dk$ denotes integration over `adelicMaximalCompact F` against [`AutomorphicForm.maximalCompactHaar F`](def/AutomorphicForm_AdelicMaximalCompact.html#L208), and $V$ is the real value of `adelicAddHaar (𝓞 F) F (adelicBox F)`, the volume of the box, so that $M_\varphi(s,g) := V^{-1} N_\varphi(s,g)$ and $M_\psi(s,g) := V^{-1} N_\psi(s,g)$.
--
--   The conclusion is a conjunction of three statements about the product
--   $$P(x) := \bigl(\Lambda^{e^R} E_\varphi(it)\bigr)(x)\cdot \overline{\bigl(\Lambda^{e^R} E_\psi(it)\bigr)(x)} ,$$
--   where $it$ abbreviates $(t : \mathbb C)\cdot i$, integrated over [`AutomorphicForm.canonicalTruncationDomain F α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) (the third component of the canonically chosen truncation datum for $(\alpha,\beta)$, empty if no such datum exists) against `adelicGLHaar (Fin 2) (𝓞 F) F`.
--
--   First conjunct: $P$ is integrable on `canonicalTruncationDomain F α β` for that Haar measure.
--
--   Second conjunct: if $\mu = \nu$, then
--   $$\int_{\text{canonicalTruncationDomain}} P \;=\; c\Bigl( \langle \varphi_{it}, \psi_{it}\rangle\,(2R) \;-\; \langle M_\varphi(it), V^{-1}\tfrac{d}{ds}N_\psi(s)\big|_{s=it}\rangle \;+\; \langle \varphi_{it}, M_\psi(it)\rangle\,\frac{e^{2iRt}}{2it} \;-\; \langle M_\varphi(it), \psi_{it}\rangle\,\frac{e^{-2iRt}}{2it} \Bigr),$$
--   with all four pairings taken over the maximal compact subgroup as above, and the derivative being the complex derivative of $s \mapsto N_\psi(s,g)$ at $s = it$, scaled by $V^{-1}$.
--
--   Third conjunct: if there exists $z$ in [`NumberField.TateGlobal.normOneIdeles F`](def/NumberField_TateGlobalZeta.html#L16) (the kernel of the module character of $\mathbb A$) with $\mu(z) \neq \nu(z)$, then
--   $$\int_{\text{canonicalTruncationDomain}} P \;=\; c\Bigl( \langle \varphi_{it}, \psi_{it}\rangle\,(2R) \;-\; \langle M_\varphi(it), V^{-1}\tfrac{d}{ds}N_\psi(s)\big|_{s=it}\rangle \Bigr),$$
--   the two oscillating cross terms being absent. The same constant $c$ and the same threshold $R_0$ serve both cases.
--
--   This is the Maass–Selberg relation for truncated Eisenstein series on $\mathrm{GL}_2$ over a number field, evaluated at the diagonal unitary parameter $s' = s = it$ with $t \neq 0$, in the polarised form for two flat induced families: the inner product of the truncations at height $e^R$ is affine in $R$ together with the oscillating terms $e^{\pm 2iRt}/(2it)$ in the diagonal case $\mu = \nu$, and purely affine when $\mu/\nu$ is non-trivial on the norm-one idele classes. It feeds the $L^2$ estimates and the limit computations for truncated Eisenstein integrals used in the spectral analysis of the automorphic quotient, and is cited by the statements producing bounds on $\int \lVert \Lambda^{e^R} E\rVert^2$ and the comparisons of truncated Eisenstein integrals with convolution sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat
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
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        φf s (k : AdelicGL2 (𝓞 F) F) = φf 0 (k : AdelicGL2 (𝓞 F) F))
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        ψf s (k : AdelicGL2 (𝓞 F) F) = ψf 0 (k : AdelicGL2 (𝓞 F) F))
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
      (t : ℝ) (_ht : t ≠ 0) (R : ℝ) (_hR : R₀ ≤ R),
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
          (Eψ ((t : ℂ) * Complex.I)) x))
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (μ = ν →
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
          (Eψ ((t : ℂ) * Complex.I)) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (c : ℂ) *
        ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) * (2 * (R : ℂ))
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F))
          + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
              Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) )) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
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
          (Eψ ((t : ℂ) * Complex.I)) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (c : ℂ) *
        ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) * (2 * (R : ℂ))
          - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) )) := by sorry
