-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/08ddf7ee-a927-5305-8710-56bf90d3264a
-- title:
--   Maass–Selberg relations on the unitary axis for flat sections
-- statement:
--   Setting. Let $L$ be a number field, let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_L$ be a subset of $\mathrm{GL}_2$ of the adele ring $\mathbb{A}=\,$`AdeleRing (𝓞 L) L`. Write $\alpha_m$ for the monoid homomorphism from $\mathbb{A}^{\times}$ to $\mathbb{R}^{\times}$ obtained from the distributive Haar character of $\mathbb{A}$ (a homomorphism into $\mathbb{R}_{\ge 0}$) by composing with the coercion $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passing to units; the adele ring is given its Borel $\sigma$-algebra. A hypothesis $h_{\alpha m}$ asserts that $\alpha_m(x)>0$ for every idele $x$.
--
--   The assertion is: there exist a real number $c_{MS}>0$ and a real number $R_0$ such that for all of the following data the four conclusions below hold.
--
--   Characters. Four monoid homomorphisms $\mu,\nu,\mu',\nu'\colon\mathbb{A}^{\times}\to\mathbb{C}^{\times}$, each of which is unitary in the sense of `IsUnitaryChar` ($\|\chi(x)\|=1$ for all $x$), each trivial on principal ideles in the sense of `IsIdeleClassChar` ($\chi$ of the image of $u\in L^{\times}$ equals $1$), and each continuous as a $\mathbb{C}$-valued function on $\mathbb{A}^{\times}$.
--
--   The family $\varphi$. A function $\varphi_f\colon\mathbb{C}\to \mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ subject to seven conditions: (i) for every $s$, $\varphi_f(s)$ is an induced section for the pair $(\mu\cdot\alpha_m^{\,s+1/2},\ \nu\cdot\alpha_m^{-(s+1/2)})$, i.e. $\varphi_f(s)(bg)=\chi_1(b_{00})\,\chi_2(b_{11})\,\varphi_f(s)(g)$ for every $b$ in the adelic Borel subgroup (lower-left entry zero) and every $g$, where $\chi_1,\chi_2$ are the two characters just named and $\alpha_m^{z}(x)=((\alpha_m x:\mathbb{R}):\mathbb{C})^{z}$; (ii) for every $s$, $\varphi_f(s)$ satisfies `IsArchKFinite L`, that is, at every infinite place $w$ it satisfies the predicate `RightTranslatesSpanFinite` for the subgroup `archRowIsometrySubgroup L w` of $\mathrm{GL}_2(\mathbb{A})$ (the image of the row-isometry subgroup of $\mathrm{GL}_2$ of the completion at $w$); (iii) for every $s$, $\varphi_f(s)$ is $K_f$-smooth: it is a smooth vector for right translation by `finiteAdelicGL2Subgroup L`, the kernel of the archimedean projection `glArch`, meaning its stabiliser there is open; (iv) $(s,g)\mapsto\varphi_f(s)(g)$ is continuous; (v) for every $g$, $s\mapsto\varphi_f(s)(g)$ is differentiable on $\mathbb{C}$; (vi) uniform finiteness: for every infinite place $w$ there is a finite-dimensional $\mathbb{C}$-submodule $W$ of functions on `archRowIsometrySubgroup L w` such that $k\mapsto\varphi_f(s)(gk)$ lies in $W$ for all $s$ and all $g$; (vii) flatness: $\varphi_f(s)(k)=\varphi_f(0)(k)$ for every $s$ and every $k$ in `adelicMaximalCompact L`, the subgroup of matrices whose finite part lies in `finiteIntegralGL2` and each of whose archimedean components is a row isometry.
--
--   The family $\psi$. A function $\psi_f$ of the same shape, satisfying the same seven conditions, with the inducing pair $(\mu'\cdot\alpha_m^{\,s+1/2},\ \nu'\cdot\alpha_m^{-(s+1/2)})$.
--
--   Continuation data. A set $O_\varphi\subseteq\mathbb{C}$ and functions $E_\varphi,N_\varphi\colon\mathbb{C}\to\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ together with a nine-clause hypothesis: $O_\varphi$ is open and preconnected, contains the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_\varphi(s)(g)$ and $s\mapsto N_\varphi(s)(g)$ are analytic on a neighbourhood of each point of $O_\varphi$; both $(s,g)\mapsto E_\varphi(s)(g)$ and $(s,g)\mapsto N_\varphi(s)(g)$ are continuous on $O_\varphi\times\mathrm{univ}$; for $\operatorname{Re}s>1/2$ and all $g$, $E_\varphi(s)(g)=\varphi_f(s)(g)+\sum_{\xi\in L}\varphi_f(s)(w\,u(\xi)\,g)$, where $w$ is `adelicWeyl` and $u(\xi)$ the upper unipotent matrix with entry the image of $\xi$ in $\mathbb{A}$; and for $\operatorname{Re}s>1/2$ and all $g$, $N_\varphi(s)(g)=\int \varphi_f(s)(w^{-1}u(x)g)\,dx$ is the Weyl intertwining integral against `adelicAddHaar`. A set $O_\psi$ and functions $E_\psi,N_\psi$ satisfying the identical nine clauses with $\psi_f$ in place of $\varphi_f$.
--
--   Finally, real numbers $t$ and $R$ with $R_0\le R$.
--
--   Truncation. For a function $F$ on $\mathrm{GL}_2(\mathbb{A})$ write $\Lambda^{R}F$ for [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) formed from the measure and measurable space recorded in the `CarrierPins` record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, whose relevant fields are the Borel $\sigma$-algebra of $\mathbb{A}$ and the conditioning of `adelicAddHaar` on the adelic box `adelicBox L` (so $\Phi_L$, the level subgroups and the Hecke generators occur only as further fields of that record), from the unipotent embedding $x\mapsto u(x)$, from the adelic height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), and from the threshold $e^{R}$; explicitly $\Lambda^{R}F(g)=F(g)-\mathbf 1_{\{h:\ e^{R}<\mathrm{ht}(h)\}}(g)\cdot\big(\text{constant term of }F\text{ at }g\big)$. All integrals over the maximal compact subgroup are taken against [`AutomorphicForm.maximalCompactHaar L`](def/AutomorphicForm_AdelicMaximalCompact.html#L208), the Haar measure of `adelicMaximalCompact L`. Write $c=\big(\mathrm{adelicAddHaar}(\mathrm{adelicBox}\,L)\big)^{\mathrm{toReal}}$, coerced into $\mathbb{C}$, and set $s_t=t\,i$.
--
--   Conclusions. First, the function
--   $$x\mapsto \Lambda^{R}\!\big(E_\varphi(s_t)\big)(x)\cdot\overline{\Lambda^{R}\!\big(E_\psi(s_t)\big)(x)}$$
--   is integrable on [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) (the third component of the canonically chosen truncation datum for $\alpha,\beta$) with respect to the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   Second, if $\mu'=\mu$, $\nu'=\nu$, $\mu=\nu$ and $t\neq 0$, then the integral of that function over the canonical truncation domain equals
--   $$c_{MS}\Big(A\cdot 2R\;-\;B\;+\;C\,\frac{e^{2iRt}}{2it}\;-\;D\,\frac{e^{-2iRt}}{2it}\Big),$$
--   where, with all integrals over $k$ in the maximal compact subgroup,
--   $A=\int \varphi_f(s_t)(k)\overline{\psi_f(s_t)(k)}\,dk$,
--   $B=\int c^{-1}N_\varphi(s_t)(k)\,\overline{c^{-1}\,\partial_s N_\psi(\cdot)(k)\big|_{s=s_t}}\,dk$ (the derivative being that of $s\mapsto N_\psi(s)(k)$ at $s_t$),
--   $C=\int \varphi_f(s_t)(k)\,\overline{c^{-1}N_\psi(s_t)(k)}\,dk$, and
--   $D=\int c^{-1}N_\varphi(s_t)(k)\,\overline{\psi_f(s_t)(k)}\,dk$.
--
--   Third, if $\mu'=\mu$, $\nu'=\nu$, there exists $z$ in the norm-one ideles [`NumberField.TateGlobal.normOneIdeles L`](def/NumberField_TateGlobalZeta.html#L16) (the kernel of the distributive Haar character) with $\mu(z)\neq\nu(z)$, and $t\neq0$, then the same integral equals $c_{MS}\,(A\cdot 2R-B)$.
--
--   Fourth, if $\mu'=\nu$, $\nu'=\mu$, there exists $z$ in the norm-one ideles with $\mu(z)\neq\nu(z)$, and $t\neq0$, then the integral equals
--   $$c_{MS}\Big(C\,\frac{e^{2iRt}}{2it}-D\,\frac{e^{-2iRt}}{2it}\Big).$$
--
--   Fifth, if there exists $z$ in the norm-one ideles with $\mu'(z)\neq\mu(z)$ or $\nu'(z)\neq\nu(z)$, and there exists $z$ in the norm-one ideles with $\mu'(z)\neq\nu(z)$ or $\nu'(z)\neq\mu(z)$, then the integral vanishes.
--
--   The constant $c_{MS}$ and the threshold $R_0$ are chosen before all the remaining data, hence are uniform in the characters, the two families, their continuations, $t$ and $R\ge R_0$.
--
--   This is Langlands' inner-product (Maass–Selberg) formula for truncated $\mathrm{GL}_2$ Eisenstein series over a number field, evaluated at equal purely imaginary spectral parameters $s=it$, for two possibly different inducing pairs of unitary idele class characters, in the normalisation where the truncation is taken at adelic height $e^{R}$ and integration is over the canonical truncation domain attached to the determinant bounds $\alpha<\beta$; the flatness of the two families of induced sections is assumed. It is the canonical-truncation-domain form of the relation, and is used by the corresponding statement over the determinant slab.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_canonicalTruncationDomain_of_flat
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L)) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ cMS : ℝ, 0 < cMS ∧ ∃ R₀ : ℝ,
    ∀ (μ ν μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 L) L μ) (_hν : IsUnitaryChar (𝓞 L) L ν)
      (_hμ' : IsUnitaryChar (𝓞 L) L μ') (_hν' : IsUnitaryChar (𝓞 L) L ν')
      (_hμF : IsIdeleClassChar (𝓞 L) L μ) (_hνF : IsIdeleClassChar (𝓞 L) L ν)
      (_hμ'F : IsIdeleClassChar (𝓞 L) L μ') (_hν'F : IsIdeleClassChar (𝓞 L) L ν')
      (_hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hμ'k : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ' x : ℂˣ) : ℂ))
      (_hν'k : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν' x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite L (φf s))
      (_hφff : ∀ s, IsKfSmooth L (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        φf s (k : AdelicGL2 (𝓞 L) L) = φf 0 (k : AdelicGL2 (𝓞 L) L))
      (ψf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite L (ψf s))
      (_hψff : ∀ s, IsKfSmooth L (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        ψf s (k : AdelicGL2 (𝓞 L) L) = ψf 0 (k : AdelicGL2 (𝓞 L) L))
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eφ s g = φf s g + ∑' ξ : L, φf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nφ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s g = ψf s g + ∑' ξ : L, ψf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (ψf s) g))
      (t : ℝ) (R : ℝ) (_hR : R₀ ≤ R),
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
          (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I))
          x) *
          conj (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (Eψ ((t : ℂ) * Complex.I))
          x))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (μ' = μ → ν' = ν → μ = ν → t ≠ 0 →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L))
            + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) )) ∧
      (μ' = μ → ν' = ν → (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z ≠ ν z) → t ≠ 0 →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) )) ∧
      (μ' = ν → ν' = μ → (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z ≠ ν z) → t ≠ 0 →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ)) / (2 * Complex.I * (t : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) / (2 * Complex.I * (t : ℂ)) )) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ' z ≠ μ z ∨ ν' z ≠ ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ' z ≠ ν z ∨ ν' z ≠ μ z) →
        (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I))
            x) *
          conj (@AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (Eψ ((t : ℂ) * Complex.I))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0) := by sorry
