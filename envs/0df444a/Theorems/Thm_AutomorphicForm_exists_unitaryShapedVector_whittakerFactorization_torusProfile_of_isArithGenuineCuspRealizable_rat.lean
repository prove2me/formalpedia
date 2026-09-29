-- Prove2me | Theorems.Thm_AutomorphicForm_exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat
-- name    : AutomorphicForm.exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/76e620c5-fd00-5ef0-98cb-bdbaf2d3be1f
-- title:
--   Shaped unitary cusp vector over ℚ with factorised Whittaker function
-- statement:
--   Throughout, $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ (written `AdelicGL2 (𝓞 ℚ) ℚ`) carries the Borel $\sigma$-algebra `glBorel`, and the conclusion is stated with $\mathrm{GL}_2(\mathbb{R})$ given its Borel $\sigma$-algebra.
--
--   Data and hypotheses. Real numbers $c,u,d_1,d_2$ and a finite set $T \subseteq \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ are given, subject to $0 < c$, $0 < d_1$ and $d_1 < d_2$. The domain in play is $D = \bigcup_{x \in T} (\cdot * x)''\,$`centreCutSiegelSet ℚ c u d₁ d₂`, the union of the right translates by the elements of $T$ of the set of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has local height at least $c$ and window datum `xWindowSq` at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$. The hypothesis `hcov` asserts `CoversModCentre ℚ D`: every $g \in \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ can be written so that $\gamma g z \in D$ for some $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ (embedded by `globalPoints`) and some central scalar $z \in (\mathbb{A}_\mathbb{Q})^\times$.
--
--   Next, $\Theta$ is a `HeckeEigensystem ℚ ℂ`, i.e. a non-zero level ideal of $\mathcal{O}_\mathbb{Q}$ together with two families $\Theta.a, \Theta.b$ of complex numbers indexed by the finite places. The hypothesis `hΘ` asserts `IsArithGenuineCuspRealizable` for $\Theta$ at the pins
--   `productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)`,
--   that is, the carrier data consisting of the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, the domain $D$, the full central subgroup $Z = \top$, the level subgroups $N \mapsto$ `levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen`, and the Borel structure on $\mathbb{A}_\mathbb{Q}$ with additive Haar measure conditioned on the adelic box `adelicBox ℚ`; by definition this says that there exists a `SmoothCuspRealizationAt` at these pins for `Θ.toRawCentral` (same level and same $a$, with $b$ replaced by $v \mapsto (\mathrm{cNorm}\,v)^{-1}\,\Theta.b\,v$) which is genuine in the sense of `IsGenuineCuspRealizationAt`.
--
--   Finally, a family $\varpi$ of elements $\varpi_v$ of the valuation ring at each finite place $v$ is given, with `hϖ` stating that the valuation of the image of $\varpi_v$ in $\mathbb{Q}_v$ is $\exp(-1)$, and `hπall` stating that this image is non-zero.
--
--   Conclusion. There exist a finite set $S$ of finite places, a real number $\sigma_0$, an integer $k_0$, a homomorphism $\omega : (\mathbb{A}_\mathbb{Q})^\times \to \mathbb{C}^\times$, a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, functions $W_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $W_f$ on `finiteAdelicGL2Subgroup ℚ` (the kernel of `glArch`, i.e. the elements with trivial archimedean component), a function $m_S$ from finite places to $\mathbb{N}$, a function $P : \mathbb{R} \to \mathbb{R}$, a real number $x_0$ and a function $H_\infty : \mathbb{C} \to \mathbb{C}$, with all of the following properties; here `whittakerCoefficient` is always taken at the pins above and against the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615), so that the $\alpha$-th coefficient of $\varphi$ at $g$ is $\int \varphi(u(x)g)\,\psi(-\alpha x)$ against the conditioned adelic measure of the pins.
--
--   (i) Central character: $\omega$ is an idele class character ($\omega$ trivial on the principal ideles coming from $\mathbb{Q}^\times$) and is unitary, $\lVert \omega(z) \rVert = 1$ for all $z$.
--
--   (ii) The vector $\varphi$: it is continuous; it satisfies `IsRapidlyDecreasingOnSiegelSets ℚ`, i.e. for all $c',u'$, all translates $t$, all $c' > 0$ and all $N \in \mathbb{N}$ there is a constant $C$ with $\lVert \varphi(g t)\rVert\,(1 + \mathrm{archHeight}(\mathrm{glArch}\,g))^N \le C$ for $g$ in `integralWindowedSiegelSet ℚ c' u'`; it is left invariant under $\mathrm{GL}_2(\mathbb{Q})$, $\varphi(\gamma g) = \varphi(g)$; and it transforms by $\omega$ under the centre, $\varphi(z g) = \omega(z)\varphi(g)$.
--
--   (iii) Cuspidality and summability: the $0$-th Whittaker coefficient of $\varphi$ vanishes at every $g$, and for every $g$ the family $a \mapsto \lVert$ $a$-th Whittaker coefficient of $\varphi$ at $g$ $\rVert$, indexed by $a \in \mathbb{Q}$, is summable.
--
--   (iv) Pure-tensor factorisation: for every $g$, the first Whittaker coefficient of $\varphi$ at $g$ equals $W_A(\mathrm{ratArchGL2}\,g) \cdot W_f(\mathrm{finFactor}\,g)$, where `ratArchGL2` is the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the archimedean component of $g$ at the infinite place of $\mathbb{Q}$ and `finFactor` is the companion finite part of $g$.
--
--   (v) The archimedean factor: $W_A(u(x)h) = e^{2\pi i x} W_A(h)$ for all $x \in \mathbb{R}$ and $h \in \mathrm{GL}_2(\mathbb{R})$, where $u(x) = \mathrm{unipotentGL2}(x)$; $W_A(h\kappa_0) = \mathrm{archWeightChar}_\mathbb{R}(k_0)(\kappa_0)\,W_A(h)$ for every $\kappa_0$ in the subgroup `rowIsometrySubgroup₀ ℝ`; and $W_A$ is continuous.
--
--   (vi) Basic properties of the finite factor: $W_f$ is measurable, and $\lVert W_f(n g)\rVert = \lVert W_f(g)\rVert$ for every $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) (the adelic unipotent subgroup intersected with `finiteAdelicGL2Subgroup ℚ`).
--
--   (vii) Unramified local behaviour off $S$. For every $v \notin S$ there is an additive character $\psi$ of $\mathbb{Q}_v$ with $\lVert \psi(x)\rVert = 1$ for all $x$, with $\psi$ trivial on the valuation ring, with some $r$ in the valuation ring such that $\psi(r/\varpi_v) \ne 1$, and such that $W_f(\mathrm{finFactor}(\iota_v(\mathrm{unipotent}\,x)\,g)) = \psi(x)\,W_f(\mathrm{finFactor}\,g)$ for all $x \in \mathbb{Q}_v$ and all $g$, where $\iota_v =$ `placeEmbed ℚ v`. Moreover, for $v \notin S$, $W_f \circ \mathrm{finFactor}$ is right invariant under $\iota_v(x)$ for every $x \in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the pullback along `localEmbed` of `finiteLevelOne` at the unit ideal), and right invariant under $\iota_v(\mathrm{unipotent}\,r)$ for every $r$ in the valuation ring at $v$.
--
--   (viii) Hecke and central relations off $S$ with the arithmetic normalisation. For every $v \notin S$ there is a family $b : \mathrm{Fin}(\mathrm{absNorm}\,v) \to \mathcal{O}_v$ such that for all $g$,
--   $$\sum_i W_f\bigl(\mathrm{finFactor}(g\,\iota_v(\mathrm{repSome}(\varpi_v, b_i)))\bigr) + W_f\bigl(\mathrm{finFactor}(g\,\iota_v(\mathrm{repInf}(\varpi_v)))\bigr) = \bigl(N(v)^{\sigma_0/2}\,\Theta.a\,v\bigr)\,W_f(\mathrm{finFactor}\,g),$$
--   where $N(v) = \mathrm{absNorm}\,v.\mathrm{asIdeal}$, $\mathrm{repSome}(\pi,\beta) = \begin{pmatrix}\pi & \beta \\ 0 & 1\end{pmatrix}$ and $\mathrm{repInf}(\pi) = \begin{pmatrix}1 & 0 \\ 0 & \pi\end{pmatrix}$; and for every $v \notin S$ and all $g$,
--   $$W_f\bigl(\mathrm{finFactor}(g\,\iota_v(\mathrm{scalarPi}(\varpi_v)))\bigr) = \bigl(N(v)^{\sigma_0}\,\Theta.b\,v / N(v)\bigr)\,W_f(\mathrm{finFactor}\,g),$$
--   with $\mathrm{scalarPi}(\pi) = \pi\,I_2$; the scalar $N(v)^{\sigma_0}\,\Theta.b\,v / N(v)$ is non-zero for every $v \notin S$.
--
--   (ix) Growth and unitarity of the table: there is a real $\kappa$ such that for every $v \notin S$ both $\lVert N(v)^{\sigma_0/2}\,\Theta.a\,v\rVert \le N(v)^\kappa$ and $\lVert N(v)^{\sigma_0}\,\Theta.b\,v/N(v)\rVert \le N(v)^\kappa$; and for every $v \notin S$, $\Theta.a\,v \cdot \overline{\Theta.b\,v} = N(v)^{1-\sigma_0}\,\overline{\Theta.a\,v}$ and $\lVert \Theta.b\,v \rVert = N(v)^{1-\sigma_0}$.
--
--   (x) Boundedness and support of $W_f$. There is $B_1$ with $\lVert W_f(g)\rVert \le B_1$ for all $g$. There is a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` such that for every $g$ in that group which (a) at each $v \notin S$ has local component $\mathrm{localAt}_v(g) = n'k'$ with $n'$ in the range of `unipotentGL2Hom` over $\mathbb{Q}_v$ and $k' \in$ `localLevelOne (𝓞 ℚ) ℚ v ⊤`, (b) satisfies $W_f(g) \ne 0$, and (c) satisfies the bottom-row condition: at every $p \notin S$ the valuation at $p$ of the finite part of the entry $(1,j)$ of $g$ is $\le 1$ for $j = 0,1$, while at every $p \in S$ the valuation of the entry $(1,0)$ is $\le \exp(-m_S(p))$ and the valuation of the entry $(1,1) - 1$ is $\le \exp(-m_S(p))$ — there exist $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h \in \mathrm{Cpt}$ with $\mathrm{localAt}_v(n g) = \mathrm{localAt}_v(h)$ for every $v \in S$. Under the same three conditions (a), (b), (c) on $g$, the idele norm `TateGlobal.ideleNorm ℚ` of $\det g$ equals $1$.
--
--   (xi) Integrability on the support shell. For every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ` and every Haar measure $\mu_{N,f}$ on `finUnipotent`, writing $\nu = \mu_f$ with density [`HaarQuotient.density finUnipotent μNFin`](def/HaarQuotient.html#L25) and writing $E$ for the set of $g$ satisfying condition (a) above together with the bottom-row condition (c): the indicator of $E$ of the function $g \mapsto (\mathrm{normSq}(W_f(g)) : \mathbb{C})$ is $\nu$-integrable, and $\nu(E \cap \{g : W_f(g) \ne 0\}) \ne 0$.
--
--   (xii) Archimedean torus profile. $P$ is measurable; for all $a_1 \ne 0$ and $a_2 > 0$,
--   $$W_A(\mathrm{upperUnit}\,a_1\,0\,a_2)\cdot \overline{W_A(\mathrm{upperUnit}\,a_1\,0\,a_2)} = P(a_1/a_2),$$
--   where $\mathrm{upperUnit}\,a_1\,0\,a_2 = \begin{pmatrix} a_1 & 0 \\ 0 & a_2\end{pmatrix}$; $P \ge 0$ everywhere; $P$ is not almost everywhere zero; for every $\sigma' > x_0$ the function $y \mapsto P(y)\,|y|^{\sigma'-2}$ is integrable; $H_\infty$ is analytic at every real point $\sigma' > -1$; $H_\infty(0) = 0$; and for every $s$ with $\mathrm{Re}\,s > \max(x_0,0)$,
--   $$H_\infty(s)\cdot\Bigl(\tfrac12\,\pi^{-s}\,\Gamma(s)\int_{\mathbb{R}} P(y)\,|y|^{s-2}\,dy\Bigr) = 1.$$
--
--   This is the automorphic-side input package for the Rankin–Selberg analysis of a cusp-realizable Hecke eigensystem over $\mathbb{Q}$: from a genuine cuspidal realization at the production pins of a covering centre-cut Siegel window it produces a single cuspidal vector whose $\psi_\mathbb{Q}$-Whittaker function is a pure tensor, with prescribed unramified local equivariance and Hecke eigenvalues off a finite set $S$, prescribed support and integrability at the places of $S$, and an explicit archimedean torus profile together with the inverse of its Mellin factor. It is consumed by [`AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat`](thm.html#AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat), which assembles the Rankin–Selberg test data over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker
open LanglandsTunnell

theorem AutomorphicForm.exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (σ₀ : ℝ) (k₀ : ℤ)
      (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
      (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
      (P : ℝ → ℝ) (x₀ : ℝ) (Hinf : ℂ → ℂ),

      IsIdeleClassChar (𝓞 ℚ) ℚ ω ∧ (∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = 1) ∧

      Continuous φ ∧ IsRapidlyDecreasingOnSiegelSets ℚ φ ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * φ g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ a g‖) ∧

      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g)) ∧

      (∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA h) ∧
      (∀ (κ₀ : GL (Fin 2) ℝ) (hκ₀ : κ₀ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA (h * κ₀) = (archWeightCharℝ k₀ ⟨κ₀, hκ₀⟩ : ℂ) * WA h) ∧
      Continuous WA ∧

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
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)))) ≠ 0) ∧

      (∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ‖((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (σ₀ / 2) : ℝ) : ℂ) * Θ.a v))‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))))‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Θ.a v * (starRingEnd ℂ) (Θ.b v) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀) : ℝ) : ℂ) * (starRingEnd ℂ) (Θ.a v) ∧
        ‖Θ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 - σ₀)) ∧

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
                  WithZero.exp (-(mS p : ℤ)))) ∧ Wf g ≠ 0} ≠ 0) ∧

      Measurable P ∧
      (∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
        WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * (starRingEnd ℂ) (WA (upperUnit a₁ 0 a₂ h₁ h₂.ne')) = ((P (a₁ / a₂) : ℝ) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ P y) ∧ (¬ ∀ᵐ y : ℝ, P y = 0) ∧
      (∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2))) ∧
      (∀ σ' : ℝ, (-1 : ℝ) < σ' → AnalyticAt ℂ Hinf (σ' : ℂ)) ∧
      Hinf 0 = 0 ∧
      (∀ s : ℂ, max x₀ 0 < s.re →
        Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1) := by sorry
