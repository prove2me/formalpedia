-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
-- name    : AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/6bd24710-eba6-5047-846a-13f6485a8151
-- title:
--   Twisted Maass–Selberg relations for truncated Eisenstein series
-- statement:
--   Fix number fields $K \subseteq L$, real numbers $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$, a set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ (written `AdelicGL2 (𝓞 L) L`), a Galois descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28) — that is, a homomorphism $\mathrm{Aut}(L/K) \to \mathrm{RingAut}(\mathbb{A}_L)$ compatible with the embedding of $L$ and acting by continuous maps — and $\sigma \in L \simeq_K L$. Fix further reals $c, u, d_1, d_2$ with $0 < c$, a compact set $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ and a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$.
--
--   The *geometric hypotheses* on $\Phi_0$ are three: `hΦ₀S` places $\Phi_0$ inside $\bigcup_{y \in T_c} (\,\cdot\, y)\,\bigl[\mathtt{centreCutSiegelSet } L\ c\ u\ d_1\ d_2\bigr]$, the union of right translates by $T_c$ of the set of $g$ whose finite part lies in the full integral subgroup, whose local heights at all infinite places are $\geq c$, whose window quantities `xWindowSq` at all infinite places are $\leq u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$; `hΦ₀s` places $\Phi_0$ inside the determinant slab $\{g : \lVert \det g \rVert_{\mathbb{A}_L} \in [\alpha,\beta]\}$, the idele norm being the module character `distribHaarChar`; and `hΦ₀` asserts that $\Phi_0$ is a fundamental domain for the range of `globalPoints (𝓞 L) L`, the image of $\mathrm{GL}_2(L)$, acting on the slab, for the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that slab.
--
--   Write $\alpha_m$ for the positive real character of $\mathbb{A}_L^\times$ obtained from `distribHaarChar` by passing through $\mathbb{R}_{\geq 0} \to \mathbb{R}$ into the units, and let `hαm` be the hypothesis that $\alpha_m$ takes strictly positive values. For $s \in \mathbb{C}$, `cpowChar αm hαm s` is the character $z \mapsto \alpha_m(z)^s$, and `etaFst μ αm hαm s`, `etaSnd ν αm hαm s` are $\mu \cdot \alpha_m^{\,s+1/2}$ and $\nu \cdot \alpha_m^{-(s+1/2)}$.
--
--   Under these hypotheses, the assertion is: there exist a real $c_{\mathrm{MS}} > 0$ and a real $R_0$ such that the following holds for all data as now listed.
--
--   The *character hypotheses*: $\mu, \nu : \mathbb{A}_L^\times \to \mathbb{C}^\times$ are unitary (`IsUnitaryChar`: $\lvert \mu(x) \rvert = 1$ for all $x$, likewise $\nu$), trivial on the principal ideles (`IsIdeleClassChar`), and continuous as $\mathbb{C}$-valued functions.
--
--   The *section-family hypotheses* for $\varphi_f : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ are seven: for every $s$, $\varphi_f(s)$ is an induced section for the pair $(\mu\alpha_m^{s+1/2},\, \nu\alpha_m^{-(s+1/2)})$, i.e. $\varphi_f(s)(bg) = \eta_1(b_{00})\eta_2(b_{11})\varphi_f(s)(g)$ for $b$ in the adelic Borel subgroup; $\varphi_f(s)$ is archimedean $K$-finite (`IsArchKFinite`: at each infinite place $w$ the right translates under `archRowIsometrySubgroup L w` span a finite-dimensional space); $\varphi_f(s)$ is $K_f$-smooth (`IsKfSmooth`: the stabiliser of the right-translation vector in `finiteAdelicGL2Subgroup L`, the kernel of `glArch`, is open); $(s,g) \mapsto \varphi_f(s)(g)$ is jointly continuous; $s \mapsto \varphi_f(s)(g)$ is entire for each $g$; the archimedean $K$-finiteness is uniform, in that for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup L w` containing $k \mapsto \varphi_f(s)(gk)$ for all $s$ and $g$; and $\varphi_f$ is *flat*, $\varphi_f(s)(k) = \varphi_f(0)(k)$ for every $s$ and every $k$ in the adelic maximal compact subgroup `adelicMaximalCompact L`. The family $\psi_f$ is subject to the same seven hypotheses.
--
--   The *continuation packages*: $O_\varphi \subseteq \mathbb{C}$ together with $E_\varphi, N_\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ satisfy the nine-clause hypothesis `_hEφ`, namely: $O_\varphi$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ the functions $s \mapsto E_\varphi(s)(g)$ and $s \mapsto N_\varphi(s)(g)$ are analytic on a neighbourhood of $O_\varphi$; both $(s,g) \mapsto E_\varphi(s)(g)$ and $(s,g) \mapsto N_\varphi(s)(g)$ are continuous on $O_\varphi \times \mathrm{univ}$; for $\mathrm{Re}\,s > 1/2$ and all $g$, $E_\varphi(s)(g) = \varphi_f(s)(g) + \sum_{\xi \in L}' \varphi_f(s)\bigl(w \cdot n(\xi) \cdot g\bigr)$ with $w$ the adelic Weyl element and $n(\xi) =$ `unipotentGL2` of the image of $\xi$; and for $\mathrm{Re}\,s > 1/2$ and all $g$, $N_\varphi(s)(g)$ is the Weyl intertwining integral $\int_{\mathbb{A}_L} \varphi_f(s)(w^{-1} n(x) g)\,dx$ for the adelic additive Haar measure. The triple $(O_\psi, E_\psi, N_\psi)$ satisfies the same nine clauses relative to $\psi_f$.
--
--   Finally $t \in \mathbb{R}$ and $R \in \mathbb{R}$ with $R_0 \leq R$.
--
--   Throughout, $\Lambda^R$ denotes [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with the measurable space and measure supplied by the carrier pins `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)` — that is, the Borel structure on $\mathbb{A}_L$ and the adelic additive Haar measure conditioned on `adelicBox L` — with the unipotent parameterisation $x \mapsto$ `unipotentGL2 x`, the height function [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) and the threshold $e^R$: thus $\Lambda^R f (g) = f(g) - \mathbf{1}_{\{\mathrm{ht} > e^R\}}(g)\, f^{\mathrm{const}}(g)$, $f^{\mathrm{const}}$ being the constant term of $f$ along that unipotent parameterisation for the conditioned measure. Write $\sigma_{\mathbb{A}}^{-1}$ for [`AutomorphicForm.sigmaAdelicAct K L D σ.symm`](def/AutomorphicForm_SigmaAdelicAction.html#L14), the map on $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D.\mathrm{act}\,\sigma^{-1}$, and set
--   $$F(x) = \Lambda^R\bigl(E_\varphi(it)\bigr)(x)\cdot \overline{\Lambda^R\bigl(y \mapsto E_\psi(it)(\sigma_{\mathbb{A}}^{-1} y)\bigr)(x)}.$$
--   For functions $a,b$ on $\mathrm{GL}_2(\mathbb{A}_L)$ write $\langle a,b\rangle = \int_{\mathbf{K}} a(k)\overline{b(k)}\,d k$ over `adelicMaximalCompact L` with measure [`AutomorphicForm.maximalCompactHaar L`](def/AutomorphicForm_AdelicMaximalCompact.html#L208), and let $v = \bigl(\mathtt{adelicAddHaar (𝓞 L) L}\,(\mathtt{adelicBox } L)\bigr)$ be the volume of the box, viewed as a complex number through its real value.
--
--   The conclusion is a conjunction of five statements.
--
--   First, $F$ is integrable on $\Phi_0$ for `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   Second (the four-term relation): if $\mu(D.\mathrm{unitsAct}\,\sigma^{-1} z) = \mu(z)$ and $\nu(D.\mathrm{unitsAct}\,\sigma^{-1} z) = \nu(z)$ for all ideles $z$, and if $\theta \in \mathbb{R}$ satisfies $\mu(z) = \nu(z)\,\alpha_m(z)^{i\theta}$ for all $z$, and $2t + \theta \neq 0$, then
--   $$\int_{\Phi_0} F = c_{\mathrm{MS}}\Bigl[ \langle \varphi_f(0), \psi_f(0)\circ\sigma_{\mathbb{A}}^{-1}\rangle \cdot 2R - \langle v^{-1}N_\varphi(it),\, \bigl(v^{-1}\partial_s N_\psi(\cdot)\bigr)(it)\circ\sigma_{\mathbb{A}}^{-1}\rangle + \langle \varphi_f(it),\, v^{-1}N_\psi(it)\circ\sigma_{\mathbb{A}}^{-1}\rangle \frac{e^{iR(2t+\theta)}}{i(2t+\theta)} - \langle v^{-1}N_\varphi(it),\, \psi_f(it)\circ\sigma_{\mathbb{A}}^{-1}\rangle \frac{e^{-iR(2t+\theta)}}{i(2t+\theta)}\Bigr],$$
--   where the derivative in the second term is $\mathrm{deriv}$ of $s \mapsto N_\psi(s)(g)$ at $it$, and the twist $\circ\,\sigma_{\mathbb{A}}^{-1}$ is applied to the second argument of each inner product.
--
--   Third (the two-term relation): if $\mu$ and $\nu$ are again invariant under $D.\mathrm{unitsAct}\,\sigma^{-1}$, if there exists $z$ in the norm-one ideles (the kernel of `distribHaarChar`) with $\mu(z) \neq \nu(z)$, and if $t \neq 0$, then $\int_{\Phi_0} F$ equals $c_{\mathrm{MS}}$ times the first two terms above, namely $\langle \varphi_f(0), \psi_f(0)\circ\sigma_{\mathbb{A}}^{-1}\rangle\cdot 2R - \langle v^{-1}N_\varphi(it), (v^{-1}\partial_s N_\psi)(it)\circ\sigma_{\mathbb{A}}^{-1}\rangle$.
--
--   Fourth (vanishing): if some idele $z$ has $\mu(D.\mathrm{unitsAct}\,\sigma^{-1} z) \neq \mu(z)$ or $\nu(D.\mathrm{unitsAct}\,\sigma^{-1} z) \neq \nu(z)$, and if for no real $\tau$ do both $\mu\circ D.\mathrm{unitsAct}\,\sigma^{-1} = \nu\cdot\alpha_m^{i\tau}$ and $\nu\circ D.\mathrm{unitsAct}\,\sigma^{-1} = \mu\cdot\alpha_m^{-i\tau}$ hold, then $\int_{\Phi_0} F = 0$.
--
--   Fifth (the cross terms): for every $\tau \in \mathbb{R}$, if $\mu(D.\mathrm{unitsAct}\,\sigma^{-1} z) = \nu(z)\,\alpha_m(z)^{i\tau}$ and $\nu(D.\mathrm{unitsAct}\,\sigma^{-1} z) = \mu(z)\,\alpha_m(z)^{-i\tau}$ for all $z$, if some $z$ has $\mu(D.\mathrm{unitsAct}\,\sigma^{-1} z) \neq \mu(z)$ or $\nu(D.\mathrm{unitsAct}\,\sigma^{-1} z) \neq \nu(z)$, and if $2t + \tau \neq 0$, then
--   $$\int_{\Phi_0} F = c_{\mathrm{MS}}\Bigl[\langle \varphi_f(it),\, v^{-1}N_\psi(it)\circ\sigma_{\mathbb{A}}^{-1}\rangle \frac{e^{iR(2t+\tau)}}{i(2t+\tau)} - \langle v^{-1}N_\varphi(it),\, \psi_f(it)\circ\sigma_{\mathbb{A}}^{-1}\rangle \frac{e^{-iR(2t+\tau)}}{i(2t+\tau)}\Bigr].$$
--
--   The constants $c_{\mathrm{MS}}$ and $R_0$ are chosen before the characters, the section families, the continuation packages, $t$ and $R$, so they are uniform in all of these.
--
--   This is the Maass–Selberg relation for the truncated inner product of an Eisenstein series on $\mathrm{GL}_2(\mathbb{A}_L)$ against the $\sigma$-translate of a second one, in the four mutually exclusive regimes of the base-change situation (both characters $\sigma$-invariant and proportional by an imaginary power of the idele norm; both $\sigma$-invariant but not proportional; the twisted pair unrelated; and the twisted pair swapped up to an imaginary power), as in Langlands' treatment of the continuous spectrum for base change for $\mathrm{GL}(2)$. It feeds the $\sigma$-twisted continuous-term package: the limit statement [`AutomorphicForm.exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_of_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct_of_isSemiLocalFactorization) cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat.lean

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

theorem AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_eq_maassSelberg_cases_slab_of_flat
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
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
    ∀ (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 L) L μ) (_hν : IsUnitaryChar (𝓞 L) L ν)
      (_hμF : IsIdeleClassChar (𝓞 L) L μ) (_hνF : IsIdeleClassChar (𝓞 L) L ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
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
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
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
          (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
          x))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = μ z) → (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = ν z) →
        ∀ θ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ z = ν z * cpowChar αm hαm ((θ : ℂ) * Complex.I) z) → 2 * t + θ ≠ 0 →
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
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf 0 (k : AdelicGL2 (𝓞 L) L) * conj (ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))
            + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (Complex.I * (R : ℂ) * (2 * (t : ℂ) + (θ : ℂ))) / (Complex.I * (2 * (t : ℂ) + (θ : ℂ)))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(Complex.I * (R : ℂ) * (2 * (t : ℂ) + (θ : ℂ)))) / (Complex.I * (2 * (t : ℂ) + (θ : ℂ))) )) ∧
      ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = μ z) → (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles L, μ z ≠ ν z) → t ≠ 0 →
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
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf 0 (k : AdelicGL2 (𝓞 L) L) * conj (ψf 0 (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) * (2 * (R : ℂ))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) )) ∧
      ((∃ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) ≠ μ z ∨ ν (D.unitsAct σ.symm z) ≠ ν z) →
        (∀ τ : ℝ, ¬ ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = ν z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) ∧
            (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = μ z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z))) →
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
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0) ∧
      (∀ τ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = ν z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = μ z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z) →
        (∃ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) ≠ μ z ∨ ν (D.unitsAct σ.symm z) ≠ ν z) → 2 * t + τ ≠ 0 →
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
            (fun y => Eψ ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
            x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        (cMS : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (Complex.I * (R : ℂ) * (2 * (t : ℂ) + (τ : ℂ))) / (Complex.I * (2 * (t : ℂ) + (τ : ℂ)))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) *
                Complex.exp (-(Complex.I * (R : ℂ) * (2 * (t : ℂ) + (τ : ℂ)))) / (Complex.I * (2 * (t : ℂ) + (τ : ℂ))) )) := by sorry
