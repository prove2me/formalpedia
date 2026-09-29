-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_slab_of_flat
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_slab_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/a168368e-f436-5f41-a76e-9f1f840802a2
-- title:
--   Maass–Selberg relations on the unitary axis, two character pairs
-- statement:
--   Setting. Let $L$ be a number field, $\mathbb{A} = \mathbb{A}_L$ its adele ring, and let $\alpha,\beta$ be reals with $0 < \alpha$ (`hα`) and $\alpha < \beta$ (`hαβ`). Let $\Phi_L$ be a subset of $\mathrm{GL}_2(\mathbb{A})$ (it enters only through the record `productionPinsOf`, whose domain field does not occur in the truncation operator used below). Let $c,u,d_1,d_2$ be reals with $0 < c$ (`hc`), let $T_c \subseteq \mathrm{GL}_2(\mathbb{A})$ be compact (`hTc`) and let $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A})$ satisfy three conditions: `hΦ₀S` says $\Phi_0$ is contained in $\bigcup_{y \in T_c} \mathfrak{S}(c,u,d_1,d_2)\,y$, where $\mathfrak{S}(c,u,d_1,d_2) =$ `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height $\ge c$ and window $\mathrm{xWindowSq} \le u^2$, and whose archimedean determinant norm at every $w$ lies in $[d_1,d_2]$; `hΦ₀s` says $\Phi_0$ lies in the determinant slab $\{g : \|\det g\|_{\mathbb{A}} \in [\alpha,\beta]\}$, the norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19); and `hΦ₀` says $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` on the Haar measure `adelicGLHaar` restricted to that slab.
--
--   Let $\alpha_m : \mathbb{A}^\times \to \mathbb{R}^\times$ be the idele-norm character, i.e. the homomorphism to units obtained from the distributive Haar character of $\mathbb{A}$ composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and let `hαm` assert that $\alpha_m(x) > 0$ for every $x$; the adele ring carries its Borel structure.
--
--   The assertion is that there exist a real $c_{MS} > 0$ and a real $R_0$ such that the following holds for all data as follows.
--
--   Characters. Four homomorphisms $\mu,\nu,\mu',\nu' : \mathbb{A}^\times \to \mathbb{C}^\times$, each unitary in the sense that $|\chi(x)| = 1$ for all $x$ (`IsUnitaryChar`), each trivial on the principal ideles $L^\times$ (`IsIdeleClassChar`), and each continuous as a $\mathbb{C}$-valued function.
--
--   Two section families. A family $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$, written $\varphi_s$, subject to: for every $s$, $\varphi_s$ is an induced section for the pair $(\mu\,\alpha_m^{\,s+1/2},\ \nu\,\alpha_m^{\,-(s+1/2)})$, i.e. $\varphi_s(bg) = \eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel subgroup, with $\eta_1 =$ `etaFst μ αm hαm s` and $\eta_2 =$ `etaSnd ν αm hαm s`; for every $s$, $\varphi_s$ is archimedean $K$-finite (at each infinite place the right translates under `archRowIsometrySubgroup` span a finite-dimensional space) and $K_f$-smooth (its stabiliser under right translation by the kernel of `glArch` is open); $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; $s \mapsto \varphi_s(g)$ is differentiable for each $g$; a uniform $K$-finiteness hypothesis holds, namely for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup L w` with $k \mapsto \varphi_s(gk) \in W$ for all $s$ and $g$; and flatness holds: $\varphi_s(k) = \varphi_0(k)$ for every $s$ and every $k$ in `adelicMaximalCompact L`. A second family $\psi_s$ satisfies the same seven hypotheses with $(\mu',\nu')$ in place of $(\mu,\nu)$.
--
--   Continuation data. A set $O_\varphi \subseteq \mathbb{C}$ and functions $E_\varphi, N_\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ together with the nine-clause hypothesis `_hEφ`: $O_\varphi$ is open and preconnected and contains both the line $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$, $s \mapsto E_\varphi(s,g)$ and $s \mapsto N_\varphi(s,g)$ are analytic on a neighbourhood of each point of $O_\varphi$; both $(s,g) \mapsto E_\varphi(s,g)$ and $(s,g) \mapsto N_\varphi(s,g)$ are continuous on $O_\varphi \times \mathrm{GL}_2(\mathbb{A})$; and for $\mathrm{Re}\,s > 1/2$ and all $g$ one has the Bruhat expansion $E_\varphi(s,g) = \varphi_s(g) + \sum_{\xi \in L} \varphi_s(w\,n(\xi)\,g)$, with $w =$ `adelicWeyl` and $n(\xi)$ the upper unipotent matrix of the image of $\xi$, and $N_\varphi(s,g) = \int_{\mathbb{A}} \varphi_s(w^{-1} n(x) g)\,dx$ against `adelicAddHaar`. Data $O_\psi, E_\psi, N_\psi$ satisfy the same nine clauses with $\psi$ in place of $\varphi$.
--
--   Finally, reals $t$ and $R$ with $R_0 \le R$.
--
--   Notation for the conclusion. Write $\Lambda^R f$ for [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) applied with the measurable space and measure supplied by `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, that is with the conditional (normalised) Haar measure of $\mathbb{A}$ on the adelic box, with unipotent parameter $x \mapsto n(x)$, with the height function [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) and with threshold $e^R$: thus $(\Lambda^R f)(g) = f(g) - \mathbf{1}_{\{\mathrm{ht}(g) > e^R\}}(g)\cdot (\text{constant term of } f)(g)$. Write $\langle f_1, f_2\rangle = \int_{\mathbf{K}} f_1(k)\overline{f_2(k)}\,dk$ for integration over $\mathbf{K} =$ `adelicMaximalCompact L` against [`AutomorphicForm.maximalCompactHaar L`](def/AutomorphicForm_AdelicMaximalCompact.html#L208), and put $q = (\mathrm{adelicAddHaar}(\mathrm{adelicBox}\ L)).\mathrm{toReal}$, viewed in $\mathbb{C}$, with $\widehat{N}_\varphi(s,g) = q^{-1}N_\varphi(s,g)$ and likewise for $\psi$. All Eisenstein data are evaluated at the unitary point $s = it$.
--
--   Conclusion (five conjuncts).
--
--   (1) The function $g \mapsto (\Lambda^R E_\varphi(it))(g)\cdot \overline{(\Lambda^R E_\psi(it))(g)}$ is integrable on $\Phi_0$ with respect to `adelicGLHaar`.
--
--   (2) If $\mu' = \mu$, $\nu' = \nu$, $\mu = \nu$ and $t \ne 0$, then
--   $$\int_{\Phi_0} (\Lambda^R E_\varphi(it))\,\overline{(\Lambda^R E_\psi(it))} = c_{MS}\Big( 2R\,\langle \varphi_{it}, \psi_{it}\rangle - \big\langle \widehat{N}_\varphi(it),\ q^{-1}\partial_s N_\psi(s,\cdot)|_{s=it}\big\rangle + \langle \varphi_{it}, \widehat{N}_\psi(it)\rangle \frac{e^{2iRt}}{2it} - \langle \widehat{N}_\varphi(it), \psi_{it}\rangle \frac{e^{-2iRt}}{2it}\Big),$$
--   where the second pairing is $\int_{\mathbf{K}} q^{-1}N_\varphi(it,k)\,\overline{q^{-1}\,\mathrm{deriv}(s \mapsto N_\psi(s,k))(it)}\,dk$.
--
--   (3) If $\mu' = \mu$, $\nu' = \nu$, there is $z$ in the norm-one ideles (the kernel of the distributive Haar character) with $\mu(z) \ne \nu(z)$, and $t \ne 0$, then the same integral equals
--   $$c_{MS}\Big( 2R\,\langle \varphi_{it}, \psi_{it}\rangle - \big\langle \widehat{N}_\varphi(it),\ q^{-1}\partial_s N_\psi(s,\cdot)|_{s=it}\big\rangle\Big).$$
--
--   (4) If $\mu' = \nu$, $\nu' = \mu$, there is $z$ in the norm-one ideles with $\mu(z) \ne \nu(z)$, and $t \ne 0$, then the same integral equals
--   $$c_{MS}\Big( \langle \varphi_{it}, \widehat{N}_\psi(it)\rangle \frac{e^{2iRt}}{2it} - \langle \widehat{N}_\varphi(it), \psi_{it}\rangle \frac{e^{-2iRt}}{2it}\Big).$$
--
--   (5) If there is $z$ in the norm-one ideles with $\mu'(z) \ne \mu(z)$ or $\nu'(z) \ne \nu(z)$, and there is $z$ in the norm-one ideles with $\mu'(z) \ne \nu(z)$ or $\nu'(z) \ne \mu(z)$, then the integral vanishes.
--
--   The constant $c_{MS}$ and the threshold $R_0$ are chosen once and for all, before the characters, the section families and the continuation data; cases (2)–(4) require $t \ne 0$, while case (5) does not.
--
--   This is Langlands' inner-product (Maass–Selberg) formula for truncated $\mathrm{GL}_2$ Eisenstein series over a number field, evaluated at equal parameters $s = it$ on the unitary axis, for two possibly different inducing pairs of unitary idele class characters, in the determinant-slab normalisation used for the trace formula here: the four-term relation when the inducing data agree and $\mu = \nu$, the two-term relation when the pairs agree but $\mu \ne \nu$ on the norm-one ideles, the cross-term relation when the pairs are swapped, and orthogonality otherwise. It is used by the variant of the same statement in which the second truncated Eisenstein series is translated by an adelic group element, which feeds the continuous spectral contribution to the trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_slab_of_flat.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_or_cross_or_zero_two_pairs_slab_of_flat
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
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
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (μ' = μ → ν' = ν → μ = ν → t ≠ 0 →
        (∫ x in Φ₀,
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
        (∫ x in Φ₀,
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
        (∫ x in Φ₀,
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
        (∫ x in Φ₀,
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
