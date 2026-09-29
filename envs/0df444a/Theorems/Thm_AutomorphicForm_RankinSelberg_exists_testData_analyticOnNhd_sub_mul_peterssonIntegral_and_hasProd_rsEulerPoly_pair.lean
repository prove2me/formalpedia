-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
-- name    : AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/321abd5c-65e8-5114-81d4-de5197e8bacc
-- title:
--   Rankin–Selberg package for a pair of cusp realisations
-- statement:
--   Throughout, $K$ is a number field, and $\alpha\colon (\mathbb{A}_K)^\times \to \mathbb{R}^\times$ denotes the adelic module character, i.e. the homomorphism obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` by viewing its values in $\mathbb{R}^\times$; thus $\alpha(t)$ is the idele norm $\lVert t\rVert =$ `ideleNorm K t`. The statement is universally quantified over a proof `hα` that $\alpha(t) > 0$ for all $t$.
--
--   **Window data.** Real numbers $c, u, d_1, d_2$ and a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_K)$ are given, subject to $0 < c$, $0 < d_1$, $d_1 < d_2$, and to `_hcov`: the set
--   $$D \;=\; \bigcup_{x \in T} \{\, g x : g \in \mathtt{centreCutSiegelSet}\ K\ c\ u\ d_1\ d_2 \,\}$$
--   satisfies `CoversModCentre K D`, that is, for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g \cdot z I \in D$. Here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and with `archDetNorm` $w\,g \in [d_1,d_2]$ for every $w$. All carrier data below is taken with respect to the pinning
--   $$\mathtt{pins} \;=\; \mathtt{productionPinsOf}\ K\ D\ \bigl(N \mapsto \mathtt{levelOne}\ N \sqcap \mathtt{finiteAdelicGL2Subgroup}\ K\bigr)\ \bigl(v \mapsto \mathtt{heckeGen}\ v\bigr)\ (\mathtt{adelicBox}\ K),$$
--   whose measurable structure and measure are the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, whose central subgroup is all of $(\mathbb{A}_K)^\times$, whose level subgroups are $\mathtt{levelOne}(N)$ intersected with the finite-adelic subgroup, whose Hecke elements are the $\mathtt{heckeGen}(v)$, and whose additive measure is the adelic Haar measure conditioned on the adelic box.
--
--   **Eigensystems and realisations.** Two Hecke eigensystems $\sigma, \tau\colon$ `HeckeEigensystem K ℂ` are given, each consisting of a nonzero level ideal of $\mathcal{O}_K$ and two families $a_v, b_v \in \mathbb{C}$ indexed by the height-one primes. For $\sigma$ there is a realisation $R_\sigma\colon$ `SmoothCuspRealizationAt K pins σ.toRawCentral`, where `σ.toRawCentral` has the same level and $a$-family as $\sigma$ and $b$-family $v \mapsto \mathrm{N}(v)^{-1} \sigma.b\,v$; such a realisation is a function $R_\sigma.\mathtt{toFun}$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which is not identically zero, together with a central character $R_\sigma.\mathtt{centralChar}$ on $(\mathbb{A}_K)^\times$, the property `IsCuspAutomorphicFnAt` together with smoothness under the finite-adelic subgroup, invariance under right translation by the level subgroup attached to $\sigma.\mathtt{level}$, a finite exceptional set $R_\sigma.\mathtt{exceptionalSet}$, the Hecke coset eigenvalue equation with eigenvalue $\sigma.a\,v$ at every $v$ outside that set, and the central eigenvalue relation $R_\sigma.\mathtt{toFun}(\mathrm{diag}(\det \mathtt{gen}(v))\,g) = \mathrm{N}(v)^{-1}\sigma.b\,v \cdot R_\sigma.\mathtt{toFun}(g)$ there. The hypothesis `_hRσ` is `IsGenuineCuspRealizationAt`, i.e. continuity of $R_\sigma.\mathtt{toFun}$. An archimedean type family $\mathtt{tys}\sigma$ and a $\mathbb{C}$-submodule $V_\sigma$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ are given with `_hVσ`: $V_\sigma$ is a cuspidal constituent for the central character $R_\sigma.\mathtt{centralChar}$, that is, a nonzero cusp subrepresentation (contained in the cuspidal $K$-finite submodule and stable under right translation by the finite-adelic subgroup, by the archimedean row-isometry subgroups, and under right convolution by archimedean-bifinite factorizable test functions) admitting no cusp subrepresentation other than $0$ and itself; and `_hRσV`: $R_\sigma.\mathtt{toFun}$ lies in $V_\sigma$, is invariant under right multiplication by the level subgroup attached to $\sigma.\mathtt{level}$, and lies in the archimedean type cut $\bigsqcap_w \bigsqcup_i \mathtt{archTypeSubmoduleAt}$ determined by $\mathtt{tys}\sigma$. The same four hypotheses `Rτ`, `_hRτ`, `_hVτ`, `_hRτV` are imposed for $\tau$, with data $\mathtt{tys}\tau$, $V_\tau$. Finally `_hw` asserts that there is a finite set $S_0$ of primes with $\lVert \sigma.b\,v\rVert = \lVert \tau.b\,v\rVert$ for all $v \notin S_0$.
--
--   **Conclusion.** There exist a finite set $S$ of height-one primes of $\mathcal{O}_K$, functions $f_x, f_y\colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, a character $\nu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$, a family $\varphi\colon \mathbb{C} \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$, real numbers $w, e_1, e_2, a, \sigma_0$, complex numbers $s_0, C$, a set $\mathcal{F} \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ and functions $A, L, \zeta_i\colon \mathbb{C} \to \mathbb{C}$ with the following properties.
--
--   For every prime $v \notin S$: $v$ divides neither $\sigma.\mathtt{level}$ nor $\tau.\mathtt{level}$, and $v$ lies in neither $R_\sigma.\mathtt{exceptionalSet}$ nor $R_\tau.\mathtt{exceptionalSet}$. Both $f_x$ and $f_y$ are factorizable test functions, i.e. products of a compactly supported smooth function of the archimedean matrix entries with a compactly supported locally constant function of the finite part. The character $\nu$ is unitary ($\lVert \nu(x)\rVert = 1$ for all $x$) and an idele class character (trivial on the image of $K^\times$). For every idele $z$,
--   $$R_\tau.\mathtt{centralChar}(z) \cdot \overline{R_\sigma.\mathtt{centralChar}(z)} \cdot \nu(z) = \lVert z\rVert^{2w},$$
--   and $\lVert R_\sigma.\mathtt{centralChar}(z)\rVert = \lVert z\rVert^{w} = \lVert R_\tau.\mathtt{centralChar}(z)\rVert$.
--
--   For every $s \in \mathbb{C}$, $\varphi(s)$ is an induced section for the pair of characters $\mathtt{etaFst}\,1 = \lVert\cdot\rVert^{s+1/2}$ and $\mathtt{etaSnd}\,\nu = \nu\,\lVert\cdot\rVert^{-(s+1/2)}$, that is, $\varphi(s)(bg) = \lVert b_{11}\rVert^{s+1/2}\,\nu(b_{22})\lVert b_{22}\rVert^{-(s+1/2)}\,\varphi(s)(g)$ for all $b$ in the adelic Borel subgroup and all $g$; moreover each $\varphi(s)$ is archimedean $K$-finite (its right translates under the archimedean row-isometry subgroup at each infinite place span a finite-dimensional space) and smooth for the finite-adelic subgroup, the map $(s,g) \mapsto \varphi(s)(g)$ is continuous, and $s \mapsto \varphi(s)(g)$ is entire for each $g$.
--
--   The slab parameters satisfy $0 < e_1 < e_2$; the set $\mathcal{F}$ is contained in $\{g : \lVert \det g\rVert \in [e_1,e_2]\}$ and is a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ on $\mathrm{GL}_2(\mathbb{A}_K)$ with respect to adelic Haar measure restricted to that slab. Furthermore $a < 1/2 < \sigma_0$ and $C \neq 0$.
--
--   The function $A$ is analytic on a neighbourhood of each point of the half-plane $\{\mathrm{Re}\,s > a\}$, and for $\mathrm{Re}\,s > 1/2$,
--   $$A(s) = (s - s_0)\cdot \mathtt{peterssonIntegral}\ K\ w\ \mathcal{F}\ \Bigl(g \mapsto x(g)\bigl(\varphi(s)(g) + \sum_{\xi \in K}\varphi(s)\bigl(w_0\,u(\xi)\,g\bigr)\bigr)\Bigr)\ y,$$
--   where $x = \mathtt{rightConv}\ K\ R_\tau.\mathtt{toFun}\ f_x$ and $y = \mathtt{rightConv}\ K\ R_\sigma.\mathtt{toFun}\ f_y$ are the right convolutions $g \mapsto \int R(gh)f(h)\,dh$, $w_0 = \mathtt{adelicWeyl}$, $u(\xi) = \mathtt{unipotentGL2}$ of the image of $\xi$, and $\mathtt{peterssonIntegral}\ K\ w\ \mathcal{F}\ X\ Y = \int_{\mathcal{F}} X(g)\overline{Y(g)}\lVert\det g\rVert^{-w}\,dg$.
--
--   The dichotomy in the parameter $s_0$: if $\nu \neq 1$ then $s_0 \neq 1/2$; and if $\nu = 1$ then $s_0 = 1/2$, $R_\tau.\mathtt{centralChar} = R_\sigma.\mathtt{centralChar}$, and $A(1/2) \neq 0$ implies that there exist $g_1, g_2 \in \mathrm{GL}_2(\mathbb{A}_K)$ with $\mathtt{peterssonIntegral}\ K\ w\ \mathcal{F}\ (h \mapsto R_\tau.\mathtt{toFun}(hg_1))\ (h \mapsto R_\sigma.\mathtt{toFun}(hg_2)) \neq 0$.
--
--   The $S$-part: the function $s \mapsto \mathtt{RankinSelberg.sPartIntegral}\ K\ S\ \mathtt{pins}\ \psi_K\ x\ y\ (\varphi(s))\ w\ e_1\ e_2$, where $\psi_K$ is the standard additive character of $\mathbb{A}_K$, is analytic on a neighbourhood of each point of $\{\mathrm{Re}\,s > a\}$, and its value at $s = 1/2$ is nonzero. Here `sPartIntegral` is the integral, over those classes $q$ in the quotient of $\mathrm{GL}_2(\mathbb{A}_K)$ by the rational centre-unipotent subgroup whose chosen representative satisfies the shell condition $\lvert \det g\rvert_v = \max(\lvert g_{21}\rvert_v, \lvert g_{22}\rvert_v)^2$ for all $v \notin S$, of the product of the indicator of $\{\lVert \det g\rVert \in [e_1,e_2]\}$, the first Whittaker coefficient of $x$, the conjugate of the first Whittaker coefficient of $y$, the value $\varphi(s)(g)$ and $\lVert \det g\rVert^{-w}$, taken with respect to the quotient measure.
--
--   The correction factor $\zeta_i$ is analytic on a neighbourhood of each point of $\{\mathrm{Re}\,s > a\}$, and for $\mathrm{Re}\,s > a$ one has $\zeta_i(s) \neq 0$ and
--   $$\prod_{v \notin S}\Bigl(1 - \tau.b\,v \cdot \overline{\sigma.b\,v}\cdot \mathrm{N}(v)^{2w-2}\cdot \mathrm{N}(v)^{-(2s+1)}\Bigr) = \zeta_i(s)$$
--   in the sense of `HasProd` over the primes outside $S$, with $\mathrm{N}(v) =$ `Ideal.absNorm v.asIdeal`.
--
--   Finally $L$ is analytic on a neighbourhood of each point of $\{\mathrm{Re}\,s > \sigma_0\}$, and for $\mathrm{Re}\,s > \sigma_0$ two assertions hold: first, the Euler product
--   $$\prod_{v \notin S}\Bigl(\mathtt{rsEulerPoly}\ \bigl(\sigma.a\,v/\sigma.b\,v\bigr)\ \bigl(\sigma.b\,v\bigr)^{-1}\ \bigl(\tau.a\,v\bigr)\ \bigl(\tau.b\,v\bigr)\ 0\Bigr)\bigl(\mathrm{N}(v)^{-(s+1/2)}\bigr)^{-1} = L(s)$$
--   in the sense of `HasProd`, where `rsEulerPoly` is the explicit degree-six polynomial of the definition; and second, the Rankin–Selberg identity
--   $$\mathtt{peterssonIntegral}\ K\ w\ \mathcal{F}\ \Bigl(g \mapsto x(g)\bigl(\varphi(s)(g) + \sum_{\xi \in K}\varphi(s)(w_0 u(\xi) g)\bigr)\Bigr)\ y \;=\; C \cdot \mathtt{sPartIntegral}(\dots,\varphi(s),\dots)\cdot \zeta_i(s)\cdot L(s),$$
--   with the same data $S$, `pins`, $\psi_K$, $x$, $y$, $w$, $e_1$, $e_2$ in the $S$-part as above.
--
--   This is the adelic Rankin–Selberg package for a pair of continuous cusp realisations on a covering centre-cut window: the integral of the two test vectors against the Eisenstein series induced from $(1,\nu)$, its regularised analytic continuation with the dichotomy according to whether the ratio $\nu$ of the unitary parts of the central characters is trivial, non-vanishing of the $S$-part at the centre, and the factorisation of the integral into the degree-six Euler product of `rsEulerPoly` times a correction factor. It is the analytic input to [`AutomorphicForm.SmoothCuspRealizationAt.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_pair_of_isCuspConstituent`](thm.html#AutomorphicForm.SmoothCuspRealizationAt.exists_lt_one_meromorphicOn_hasProd_rsEulerPoly_and_agreesAwayFromFinite_pair_of_isCuspConstituent), which extracts from it the meromorphy and rigidity statement comparing the two eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
      (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
      (σ τ : HeckeEigensystem K ℂ)
      (Rσ : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.toRawCentral)
      (_hRσ : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.toRawCentral Rσ)
      (Rτ : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.toRawCentral)
      (_hRτ : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.toRawCentral Rτ)
      (tysσ : AutomorphicForm.ArchTypeFamily K)
      (Vσ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hVσ : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Rσ.centralChar Vσ)
      (_hRσV : Rσ.toFun ∈ Vσ ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) σ.level ⊓ archCutSubmodule K tysσ)
      (tysτ : AutomorphicForm.ArchTypeFamily K)
      (Vτ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hVτ : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Rτ.centralChar Vτ)
      (_hRτV : Rτ.toFun ∈ Vτ ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) τ.level ⊓ archCutSubmodule K tysτ)
      (_hw : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S₀, ‖σ.b v‖ = ‖τ.b v‖),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (fx fy : AdelicGL2 (𝓞 K) K → ℂ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (w e₁ e₂ a σ₀ : ℝ) (s₀ C : ℂ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (A L ζi : ℂ → ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ¬ v.asIdeal ∣ σ.level ∧ ¬ v.asIdeal ∣ τ.level ∧ v ∉ Rσ.exceptionalSet ∧ v ∉ Rτ.exceptionalSet) ∧
      IsFactorizableTestFn K fx ∧ IsFactorizableTestFn K fy ∧
      IsUnitaryChar (𝓞 K) K ν ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (starRingEnd ℂ) ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((ideleNorm K z ^ (2 * w) : ℝ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧ (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      0 < e₁ ∧ e₁ < e₂ ∧
      𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      a < 1 / 2 ∧ 1 / 2 < σ₀ ∧ C ≠ 0 ∧

      AnalyticOnNhd ℂ A {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → A s = (s - s₀) * peterssonIntegral K w 𝓕
          (fun g => rightConv K Rτ.toFun fx g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K Rσ.toFun fy)) ∧

      (ν ≠ 1 → s₀ ≠ 1 / 2) ∧
      (ν = 1 → s₀ = 1 / 2 ∧ Rτ.centralChar = Rσ.centralChar ∧
        (A (1 / 2) ≠ 0 → ∃ g₁ g₂ : AdelicGL2 (𝓞 K) K,
          peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * g₁)) (fun h => Rσ.toFun (h * g₂)) ≠ 0)) ∧

      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ s) w e₁ e₂) {s : ℂ | a < s.re} ∧
      RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ (1 / 2)) w e₁ e₂ ≠ 0 ∧

      AnalyticOnNhd ℂ ζi {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, a < s.re → ζi s ≠ 0 ∧
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          (1 - τ.b v.1 * (starRingEnd ℂ) (σ.b v.1) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((2 * w - 2 : ℂ)) *
            ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) (ζi s)) ∧

      AnalyticOnNhd ℂ L {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (σ.a v.1 / σ.b v.1) (σ.b v.1)⁻¹
              (τ.a v.1) (τ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) (L s) ∧
        peterssonIntegral K w 𝓕
          (fun g => rightConv K Rτ.toFun fx g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K Rσ.toFun fy) =
        C * RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ s) w e₁ e₂ * ζi s * L s) := by sorry
