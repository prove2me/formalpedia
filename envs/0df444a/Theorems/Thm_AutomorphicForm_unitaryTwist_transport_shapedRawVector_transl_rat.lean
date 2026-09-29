-- Prove2me | Theorems.Thm_AutomorphicForm_unitaryTwist_transport_shapedRawVector_transl_rat
-- name    : AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b7a5d8f2-d4d3-5ff7-aa3e-de860848bd5a
-- title:
--   Unitary twist transports the shaped Whittaker package over ℚ
-- statement:
--   Throughout, $\|\cdot\|$ denotes `TateGlobal.ideleNorm ℚ`, the idele norm on $(\mathbb{A}_{\mathbb{Q}})^{\times}$ defined through the distributive Haar character; for a finite place $v$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$) $N(v)$ denotes `Ideal.absNorm v.asIdeal`, and $\varpi_v$ the chosen element of the local integers below. Elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ are written $g$; `ratArchGL2 g` is its component in $\mathrm{GL}_2(\mathbb{R})$ at the unique infinite place, `finFactor g` is the element $(\iota(\mathrm{ratArchGL2}\,g))^{-1}g$ of `finiteAdelicGL2Subgroup ℚ` (the kernel of `glArch`, i.e. the elements with trivial archimedean component), where $\iota$ is the archimedean inclusion `archRealGLAt`. Local matrices are $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ (`unipotent`), $\mathrm{repSome}(\pi,\beta)=\begin{pmatrix}\pi&\beta\\0&1\end{pmatrix}$, $\mathrm{repInf}(\pi)=\begin{pmatrix}1&0\\0&\pi\end{pmatrix}$, $\mathrm{scalarPi}(\pi)=\begin{pmatrix}\pi&0\\0&\pi\end{pmatrix}$, pushed into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ by `placeEmbed ℚ v`.
--
--   The data are: real numbers $c,u,d_1,d_2$ and a finite set $T\subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with $0<c$, $0<d_1$, $d_1<d_2$, subject to the covering hypothesis `hcov`: the window $D:=\bigcup_{x\in T}(\,\cdot\,x)\bigl(\mathrm{centreCutSiegelSet}\,\mathbb{Q}\,c\,u\,d_1\,d_2\bigr)$ covers $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ modulo left $\mathrm{GL}_2(\mathbb{Q})$ and the adelic centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an idele $z$ with $\gamma g\,z\in D$; here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean local heights are $\ge c$, whose window quantities `xWindowSq` are $\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$. Further data: a Hecke eigensystem $\Theta$ over $\mathbb{C}$ (a nonzero level ideal together with families $\Theta.a,\Theta.b$ of complex numbers indexed by the finite places); a character $\xi$ of the central subgroup of `productionPinsGeneral ℚ`, which is all of $(\mathbb{A}_{\mathbb{Q}})^{\times}$, with values in $\mathbb{C}^{\times}$; a real number $\sigma_0$ with $|\xi(z)|=\|z\|^{\sigma_0}$ for every idele $z$ (hypothesis `hσ₀`); a finite set $S$ of finite places; a function $m_S$ from finite places to $\mathbb{N}$; elements $\varpi_v$ of $\mathcal{O}_v$ with $v(\varpi_v)=\exp(-1)$ (`hϖ`) and $\varpi_v\neq 0$ in $\mathbb{Q}_v$ (`hπall`).
--
--   The seed datum is a function $\varphi_0$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ which is continuous (`hφ₀c`), satisfies `IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₀` (membership in the space cut out by the predicate `LsXiMemberAt` for the measurable space, Haar measure, window set and central character data packaged in `productionPinsGeneral ℚ`, together with vanishing of the constant term along the unipotent one-parameter subgroup), and is reproduced by right convolution against a factorisable test function: `hrep₀` asserts the existence of $\alpha$ with $\alpha(g)=\alpha_\infty(\mathrm{glArch}\,g)\,\alpha_f(\mathrm{glFin}\,g)$, $\alpha_\infty$ smooth of compact support in the matrix entries and $\alpha_f$ locally constant of compact support, such that $\mathrm{rightConv}\,\varphi_0\,\alpha=\varphi_0$. Here `productionPinsGeneral ℚ` is `productionPinsOf` applied to the class-representative Siegel window with constants $1/2,1,1/2,2$, the level subgroups $N\mapsto \mathrm{levelOne}\sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen`, and the box `adelicBox`; its central subgroup is $\top$, its measure the adelic $\mathrm{GL}_2$-Haar measure, and its additive measure $\nu$ the adelic additive Haar measure conditioned on `adelicBox`. Functions $\varphi_1$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $W_{A,0}$ on $\mathrm{GL}_2(\mathbb{R})$, and $W_{f,1},W_{f,0}$ on `finiteAdelicGL2Subgroup ℚ` are given, with `hfac₀`: the first Whittaker coefficient of $\varphi_0$ at the pins `productionPinsGeneral ℚ` and the standard adelic additive character `psiQ` factorises as $W_{A,0}(\mathrm{ratArchGL2}\,g)\,W_{f,0}(\mathrm{finFactor}\,g)$; and `hWA₀`: $W_{A,0}$ is not identically zero. (The Whittaker coefficient of $\varphi$ at $\alpha\in\mathbb{Q}$ is $\int \varphi(u(x)g)\,\psi_{\mathbb{Q}}(-\alpha x)\,d\nu(x)$, and depends on the pins only through the additive measure $\nu$, which is the same conditioned measure for all uses of `productionPinsOf` with box `adelicBox` below.)
--
--   For $g\in$ `finiteAdelicGL2Subgroup ℚ` write $(I_g)$ for the Iwasawa-type condition: at every $v\notin S$, `localAt ℚ v g` is a product $n'k'$ with $n'$ in the range of `unipotentGL2Hom` over $\mathbb{Q}_v$ and $k'\in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along `localEmbed` of the finite-adelic level-one subgroup for the unit ideal). Write $(V_g)$ for the second-row conditions: at every $p\notin S$ the $p$-components of both entries $g_{1j}$ have valuation $\le 1$, and at every $p\in S$ the $p$-component of $g_{10}$ has valuation $\le\exp(-m_S(p))$ and that of $g_{11}-1$ has valuation $\le\exp(-m_S(p))$.
--
--   The hypothesis `hraw` is the untwisted shaped package for $(\varphi_1,W_{A,0},W_{f,1},m_S)$; it asserts, conjunct by conjunct: $\varphi_1$ is continuous; $\varphi_1$ satisfies `IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ`; $\varphi_1$ is a finite complex linear combination $\sum_i c_i\varphi_0(\,\cdot\,g_i)$ of right translates of $\varphi_0$ by elements $g_i$ of `finiteAdelicGL2Subgroup ℚ`; $\varphi_1(zg)=\xi(z)\varphi_1(g)$ for all ideles $z$; the zeroth Whittaker coefficient of $\varphi_1$ vanishes identically; for every $g$ the family $a\mapsto\|$Whittaker coefficient of $\varphi_1$ at $a\|$ is summable over $\mathbb{Q}$; the first Whittaker coefficient of $\varphi_1$ equals $W_{A,0}(\mathrm{ratArchGL2}\,g)\,W_{f,1}(\mathrm{finFactor}\,g)$; $W_{f,1}$ is measurable; $\|W_{f,1}(ng)\|=\|W_{f,1}(g)\|$ for $n\in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); for $v\notin S$ there is a unitary additive character $\psi$ of $\mathbb{Q}_v$, trivial on $\mathcal{O}_v$ and nontrivial on $\varpi_v^{-1}\mathcal{O}_v$, with $W_{f,1}(\mathrm{finFactor}(u(x)g))=\psi(x)W_{f,1}(\mathrm{finFactor}\,g)$; $W_{f,1}\circ\mathrm{finFactor}$ is right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) and under the unipotents $u(r)$, $r\in\mathcal{O}_v$, at every $v\notin S$; for $v\notin S$ there are $b_i\in\mathcal{O}_v$, $i\in\mathrm{Fin}(N(v))$, with $\sum_i W_{f,1}(\mathrm{finFactor}(g\,\mathrm{repSome}(\varpi_v,b_i)))+W_{f,1}(\mathrm{finFactor}(g\,\mathrm{repInf}(\varpi_v)))=\Theta.a\,v\cdot W_{f,1}(\mathrm{finFactor}\,g)$; for $v\notin S$, $W_{f,1}(\mathrm{finFactor}(g\,\mathrm{scalarPi}(\varpi_v)))=(\Theta.b\,v/N(v))\,W_{f,1}(\mathrm{finFactor}\,g)$; there is a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` such that any $g$ with $(I_g)$, $W_{f,1}(g)\neq 0$ and $(V_g)$ admits $n\in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h\in \mathrm{Cpt}$ with $\mathrm{localAt}\,v\,(ng)=\mathrm{localAt}\,v\,h$ for all $v\in S$; any such $g$ has $\|\det g\|=1$; and for every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ` and every Haar measure $\mu_{N}$ on `finUnipotent`, the indicator of $\{g:(I_g)\wedge(V_g)\}$ times $g\mapsto \mathrm{normSq}(W_{f,1}(g))$ is integrable for $\mu_f$ weighted by the density [`HaarQuotient.density finUnipotent`](def/HaarQuotient.html#L25) $\mu_N$, and that weighted measure of $\{g:(I_g)\wedge(V_g)\wedge W_{f,1}(g)\neq 0\}$ is nonzero.
--
--   Put
--   $$\varphi(g)=\varphi_1(g)\,\|\det g\|^{-\sigma_0/2},\qquad W_f(x)=W_{f,1}(x)\,\|\det x\|^{-\sigma_0/2},\qquad W_A(h)=W_{A,0}(h)\,|\det h|^{-\sigma_0/2},$$
--   the last for $h\in\mathrm{GL}_2(\mathbb{R})$ with the ordinary real absolute value. The conclusion is the conjunction of the following.
--
--   (1) $\varphi$ is continuous. (2) $\varphi$ is rapidly decreasing on Siegel sets: for all $c',u'$ and $t\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with $0<c'$ and every $N\in\mathbb{N}$ there is $C$ with $\|\varphi(gt)\|\,(1+\mathrm{archHeight}(\mathrm{glArch}\,g))^N\le C$ for all $g$ in the integral windowed Siegel set with parameters $c',u'$. (3) $\varphi(\gamma g)=\varphi(g)$ for all $\gamma\in\mathrm{GL}_2(\mathbb{Q})$, embedded by `globalPoints`. (4) $\varphi(zg)=\bigl(\xi(z)\,\|z\|^{-\sigma_0}\bigr)\varphi(g)$ for every idele $z$, the central character of $\varphi$ thus being unitary. (5)–(7) At the pins `productionPinsOf ℚ` formed from the window $D$, the level subgroups $N\mapsto\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the generators `heckeGen` and the box `adelicBox`, and with the character `psiQ`: the zeroth Whittaker coefficient of $\varphi$ vanishes identically; for every $g$ the norms of the Whittaker coefficients of $\varphi$ are summable over $a\in\mathbb{Q}$; and the first Whittaker coefficient factorises as $W_A(\mathrm{ratArchGL2}\,g)\,W_f(\mathrm{finFactor}\,g)$. (8) $W_f$ is measurable. (9) $\|W_f(ng)\|=\|W_f(g)\|$ for every $n\in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43). (10) For every $v\notin S$ there is an additive character $\psi$ of $\mathbb{Q}_v$ of absolute value $1$, trivial on $\mathcal{O}_v$, with $\psi(r/\varpi_v)\neq 1$ for some $r\in\mathcal{O}_v$, such that $W_f(\mathrm{finFactor}(u(x)g))=\psi(x)\,W_f(\mathrm{finFactor}\,g)$ for all $x\in\mathbb{Q}_v$ and all $g$. (11) For $v\notin S$, $W_f(\mathrm{finFactor}(g\,k))=W_f(\mathrm{finFactor}\,g)$ for $k\in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178). (12) For $v\notin S$, $W_f(\mathrm{finFactor}(g\,u(r)))=W_f(\mathrm{finFactor}\,g)$ for $r\in\mathcal{O}_v$. (13) For $v\notin S$ there exist $b_i\in\mathcal{O}_v$, $i\in\mathrm{Fin}(N(v))$, with
--   $$\sum_i W_f\bigl(\mathrm{finFactor}(g\,\mathrm{repSome}(\varpi_v,b_i))\bigr)+W_f\bigl(\mathrm{finFactor}(g\,\mathrm{repInf}(\varpi_v))\bigr)=N(v)^{\sigma_0/2}\,\Theta.a\,v\cdot W_f(\mathrm{finFactor}\,g)$$
--   for all $g$. (14) For $v\notin S$ and all $g$, $W_f(\mathrm{finFactor}(g\,\mathrm{scalarPi}(\varpi_v)))=N(v)^{\sigma_0}\bigl(\Theta.b\,v/N(v)\bigr)W_f(\mathrm{finFactor}\,g)$. (15) $W_f$ is bounded: there is $B_1\in\mathbb{R}$ with $\|W_f(g)\|\le B_1$ for all $g$. (16) There is a compact set $\mathrm{Cpt}\subseteq$ `finiteAdelicGL2Subgroup ℚ` such that every $g$ satisfying $(I_g)$, $W_f(g)\neq 0$ and $(V_g)$ admits $n\in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h\in\mathrm{Cpt}$ with $\mathrm{localAt}\,v\,(ng)=\mathrm{localAt}\,v\,h$ for all $v\in S$. (17) Every $g$ satisfying $(I_g)$, $W_f(g)\neq 0$ and $(V_g)$ has $\|\det g\|=1$. (18) For every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ` and every Haar measure $\mu_N$ on `finUnipotent`, the indicator of $\{g:(I_g)\wedge (V_g)\}$ times $g\mapsto\mathrm{normSq}(W_f(g))$, viewed as a complex-valued function, is integrable with respect to $\mu_f$ weighted by the density [`HaarQuotient.density finUnipotent`](def/HaarQuotient.html#L25) $\mu_N$, and that weighted measure of $\{g:(I_g)\wedge(V_g)\wedge W_f(g)\neq 0\}$ is nonzero.
--
--   Thus the twist by $\|\det\|^{-\sigma_0/2}$ carries the raw package to the same package with unitary central character, with the Hecke and central eigenvalues rescaled by $N(v)^{\sigma_0/2}$ and $N(v)^{\sigma_0}$ respectively, and with the additional boundedness clause (15); the support, unit-determinant and integrability clauses are unchanged in shape.
--
--   This is the unitarisation step in the adelic Rankin–Selberg input for the Langlands–Tunnell argument: a cusp form with central character of modulus $\|\cdot\|^{\sigma_0}$ together with its Whittaker factorisation is replaced by its twist by $\|\det\|^{-\sigma_0/2}$, which has unitary central character, and every clause of the shaped package — automorphy, rapid decay on Siegel sets, Whittaker factorisation, local unramified relations at places outside $S$, support and integrability at $S$ — is transported, with the Hecke and central values rescaled by powers of the residue norm. It feeds the construction of the unitary shaped vector used to realise an arithmetic cuspidal Hecke eigensystem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_unitaryTwist_transport_shapedRawVector_transl_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem AutomorphicForm.unitaryTwist_transport_shapedRawVector_transl_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (σ₀ : ℝ)
    (hσ₀ : ∀ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      ‖((ξ.comp Subgroup.topEquiv.symm.toMonoidHom x : ℂˣ) : ℂ)‖ = TateGlobal.ideleNorm ℚ x ^ σ₀)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ₀c : Continuous φ₀)
    (hφ₀ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₀)
    (hrep₀ : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₀ α = φ₀)
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ) (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Wf₀ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hfac₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₀ 1 g =
        WA₀ (ratArchGL2 g) * Wf₀ (finFactor g))
    (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (hraw : Continuous φ₁ ∧
        IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁ ∧
        (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ₁ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
        (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g) ∧
        (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 0 g = 0) ∧
        (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ a g‖) ∧
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 g = WA₀ (ratArchGL2 g) * Wf₁ (finFactor g)) ∧
        Measurable Wf₁ ∧
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf₁ ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf₁ g‖) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
          (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
          (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
          (∃ r : v.adicCompletionIntegers ℚ,
            ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
              algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
          ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            Wf₁ (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf₁ (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf₁ (finFactor (g * placeEmbed ℚ v x)) = Wf₁ (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf₁ (finFactor (g * placeEmbed ℚ v
            (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf₁ (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
            (∑ i, Wf₁ (finFactor (g * placeEmbed ℚ v
                (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
              Wf₁ (finFactor (g * placeEmbed ℚ v
                (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            Θ.a v * Wf₁ (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf₁ (finFactor (g * placeEmbed ℚ v
            (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf₁ (finFactor g)) ∧
        (∃ Cpt : Set (finiteAdelicGL2Subgroup ℚ), IsCompact Cpt ∧
          ∀ g : finiteAdelicGL2Subgroup ℚ,
            (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
              ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
            Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                    WithZero.exp (-(mS p : ℤ)) ∧
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                    WithZero.exp (-(mS p : ℤ)))) →
              ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
                ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                  localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                    localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ,
            (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
              ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
            Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                    WithZero.exp (-(mS p : ℤ)) ∧
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                    WithZero.exp (-(mS p : ℤ)))) →
              TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) ∧
        (∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
          (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
          Integrable ({g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
              ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                    WithZero.exp (-(mS p : ℤ)) ∧
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                    WithZero.exp (-(mS p : ℤ))))}.indicator
              fun g : finiteAdelicGL2Subgroup ℚ => (Complex.normSq (Wf₁ g) : ℂ))
            (μf.withDensity (HaarQuotient.density finUnipotent μNFin)) ∧
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin))
            {g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
              ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
              (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                    WithZero.exp (-(mS p : ℤ)) ∧
                Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                    WithZero.exp (-(mS p : ℤ)))) ∧ Wf₁ g ≠ 0} ≠ 0)) :
    let φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ₁ g * ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (-σ₀ / 2) : ℝ) : ℂ))
    let Wf : finiteAdelicGL2Subgroup ℚ → ℂ := (fun x : finiteAdelicGL2Subgroup ℚ => Wf₁ x *
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (x : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (-σ₀ / 2) : ℝ) : ℂ))
    let WA : GL (Fin 2) ℝ → ℂ := (fun h : GL (Fin 2) ℝ => WA₀ h * (((|((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ)| ^ (-σ₀ / 2) : ℝ)) : ℂ))
    Continuous φ ∧
      IsRapidlyDecreasingOnSiegelSets ℚ φ ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) =
        (((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ z ^ (-σ₀) : ℝ) : ℂ)) * φ g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ a g‖) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g)) ∧
      Measurable Wf ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf g‖) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ i, Wf (finFactor (g * placeEmbed ℚ v
              (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
            Wf (finFactor (g * placeEmbed ℚ v
              (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (σ₀ / 2) : ℝ) : ℂ) * Θ.a v)) * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)))) * Wf (finFactor g)) ∧
      (∃ B₁ : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g‖ ≤ B₁) ∧
      (∃ Cpt : Set (finiteAdelicGL2Subgroup ℚ), IsCompact Cpt ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) ∧
      (∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
        Integrable ({g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ))))}.indicator
            fun g : finiteAdelicGL2Subgroup ℚ => (Complex.normSq (Wf g) : ℂ))
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin)) ∧
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin))
          {g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) ∧ Wf g ≠ 0} ≠ 0) := by sorry
