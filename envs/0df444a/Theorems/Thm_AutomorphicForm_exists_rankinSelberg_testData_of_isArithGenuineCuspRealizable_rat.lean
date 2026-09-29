-- Prove2me | Theorems.Thm_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
-- name    : AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/88996495-218c-5cdc-921a-a1bae84d5229
-- title:
--   Rankin–Selberg test data over ℚ for a cusp-realizable eigensystem
-- statement:
--   Throughout, $\mathbb{A}$ denotes the adele ring of $\mathbb{Q}$, $\mathrm{GL}_2(\mathbb{A})$ is `AdelicGL2 (𝓞 ℚ) ℚ`, and `finiteAdelicGL2Subgroup ℚ` is the kernel of the archimedean projection `glArch`, i.e. the subgroup of elements with trivial archimedean component. For $g\in\mathrm{GL}_2(\mathbb{A})$, `ratArchGL2 g` is the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the component of $g$ at the unique infinite place of $\mathbb{Q}$ under the identification of that completion with $\mathbb{R}$, and `finFactor g` is the complementary finite factor $\bigl(\text{archimedean embedding of } \mathtt{ratArchGL2}\,g\bigr)^{-1}g$, an element of `finiteAdelicGL2Subgroup ℚ`. Measurability assertions about functions on $\mathrm{GL}_2(\mathbb{R})$ are with respect to the Borel $\sigma$-algebra.
--
--   The data are real numbers $c,u,d_1,d_2$, a finite subset $T\subseteq\mathrm{GL}_2(\mathbb{A})$ and a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex coefficients, i.e. a nonzero level ideal together with functions $v\mapsto\Theta.a\,v$, $v\mapsto\Theta.b\,v$ on the primes of $\mathbb{Z}$. Write $\mathcal{D}_T:=\bigcup_{x\in T}\{y\,x : y\in \mathtt{centreCutSiegelSet}\ \mathbb{Q}\ c\ u\ d_1\ d_2\}$, the union of right translates by elements of $T$ of the centre-cut Siegel set consisting of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and window square at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$.
--
--   The hypotheses are: $0<c$, $0<d_1$, $d_1<d_2$; the covering hypothesis `hcov`, namely that $\mathcal{D}_T$ covers $\mathrm{GL}_2(\mathbb{A})$ modulo $\mathrm{GL}_2(\mathbb{Q})$ on the left and the adelic centre on the right (for every $g$ there are $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and $z\in\mathbb{A}^\times$ with $\gamma g\,z\in\mathcal{D}_T$); and the hypothesis `hΘ` that $\Theta$ is arithmetically genuinely cusp-realizable at the production pins built from $\mathcal{D}_T$, the level subgroups $N\mapsto \mathtt{levelOne}\ N\sqcap\mathtt{finiteAdelicGL2Subgroup}\ \mathbb{Q}$, the Hecke elements $v\mapsto\mathtt{heckeGen}\ v$ and the adelic box. Here the production pins carry the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A})$, the domain $\mathcal{D}_T$, the full central subgroup, the above levels and Hecke elements, the Borel $\sigma$-algebra on $\mathbb{A}$, and the measure $\nu$ obtained by conditioning the additive adelic Haar measure on the adelic box; and arithmetic genuine cusp-realizability of $\Theta$ means genuine cusp-realizability, at these pins, of the renormalised eigensystem `Θ.toRawCentral` with the same level and same $a$ and with $b$ replaced by $v\mapsto(\mathtt{cNorm}\ v)^{-1}\Theta.b\,v$: there exists a smooth cusp realization at the pins for that eigensystem which is genuine.
--
--   The conclusion asserts the existence of: a finite set $S$ of primes of $\mathbb{Z}$; functions $\varphi,\varphi':\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$; functions $W_A,W_A',F_A:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$; functions $W_f,W_f',F_f$ on `finiteAdelicGL2Subgroup ℚ`; a function $\Phi$ on $\mathbb{A}^2$; a homomorphism $\omega:\mathbb{A}^\times\to\mathbb{C}^\times$; a function $P:\mathbb{R}\to\mathbb{R}$, reals $x_0,x_H$ and a function $H_\infty:\mathbb{C}\to\mathbb{C}$; elements $\varpi_v$ of the valuation ring at $v$ for every prime $v$, together with a proof $h_\pi$ that the image of $\varpi_v$ in the completion is nonzero for every $v\notin S$; functions $\lambda,\varpi^{\mathrm{tor}},\lambda',\varpi'^{\mathrm{tor}}$ on primes (written `lam`, `om`, `lam'`, `om'`) and a real $\kappa$; a set $D\subseteq\mathrm{GL}_2(\mathbb{A})$, reals $e_1,e_2,c_S,u_S$ and a finite set $t_S\subseteq\mathrm{GL}_2(\mathbb{A})$, such that all of the following hold.
--
--   Automorphy and growth: $\varphi$ and $\varphi'$ are continuous; each is rapidly decreasing on Siegel sets, in the sense that for all $c',u'$, all $t\in\mathrm{GL}_2(\mathbb{A})$ with $0<c'$ and every $N\in\mathbb{N}$ there is a bound $C$ with $\|\varphi(gt)\|\,(1+\mathtt{archHeight}(g))^N\le C$ for all $g$ in the integral windowed Siegel set of parameters $c',u'$; and both are left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$: $\varphi(\gamma g)=\varphi(g)$ and $\varphi'(\gamma g)=\varphi'(g)$.
--
--   Central character: $\omega$ is an idele class character, i.e. trivial on the image of $\mathbb{Q}^\times$; and $\varphi(z g)=\omega(z)\varphi(g)$, $\varphi'(z g)=\omega^{-1}(z)\varphi'(g)$ for central $z\in\mathbb{A}^\times$.
--
--   Whittaker expansions: the Whittaker coefficient of $\varphi'$ at the additive character $\psi_{\mathbb{Q}}^{-1}$ and index $0$ vanishes at every $g$, where the Whittaker coefficient of a function $\phi$ at $\psi$ and index $\alpha\in\mathbb{Q}$ is $\int\phi(n(x)g)\,\psi(-\alpha x)\,d\nu(x)$ with $n(x)$ the upper unipotent matrix and $\nu$ the conditional measure attached to the pins; for every $g$, the family of norms of the Whittaker coefficients of $\varphi$ at $\psi_{\mathbb{Q}}$, indexed by $a\in\mathbb{Q}$, is summable, and likewise for $\varphi'$ at $\psi_{\mathbb{Q}}^{-1}$.
--
--   Schwartz–Bruhat section and fundamental domain: $\Phi$ lies in the span `schwartzBruhat2 ℚ` of pure tensors of a Schwartz function on the mixed space with a locally constant compactly supported function on the finite adeles; $0<e_1$, $e_1<e_2$, $0<c_S$; $D$ is measurable of finite adelic Haar volume, contained in the slab $\{g:\|\det g\|_{\mathbb{A}}\in[e_1,e_2]\}$, is a fundamental domain for the image of $\mathrm{GL}_2(\mathbb{Q})$ with respect to the adelic Haar measure restricted to that slab, and is contained in $\bigcup_{t\in t_S}$ of the right translates by $t$ of the integral windowed Siegel set of parameters $c_S,u_S$.
--
--   Pure-tensor factorisations: for every $g$, the Whittaker coefficient of $\varphi$ at $\psi_{\mathbb{Q}}$ and index $1$ equals $W_A(\mathtt{ratArchGL2}\,g)\,W_f(\mathtt{finFactor}\,g)$; the Whittaker coefficient of $\varphi'$ at $\psi_{\mathbb{Q}}^{-1}$ and index $1$ equals $W_A'(\mathtt{ratArchGL2}\,g)\,W_f'(\mathtt{finFactor}\,g)$; and $\Phi$ evaluated on the bottom row vector of $g$ at $1$ equals $F_A(\mathtt{ratArchGL2}\,g)\,F_f(\mathtt{finFactor}\,g)$, where moreover $F_A(g)=\exp\bigl(-\pi(g_{10}^2+g_{11}^2)\bigr)$ for every $g\in\mathrm{GL}_2(\mathbb{R})$. The functions $W_A$, $W_A'$, $P$, $W_f$, $W_f'$, $F_f$ are measurable.
--
--   Archimedean invariance and torus profile: $W_AW_A'$ is invariant under left multiplication by the unipotent subgroup `realUnipotent` of $\mathrm{GL}_2(\mathbb{R})$ and under right multiplication by elements of `rowIsometrySubgroup ℝ` of determinant $1$; for $a_1\neq 0$ and $a_2>0$ one has $W_A\bigl(\mathtt{upperUnit}\,a_1\,0\,a_2\bigr)W_A'\bigl(\mathtt{upperUnit}\,a_1\,0\,a_2\bigr)=P(a_1/a_2)$, where $\mathtt{upperUnit}\,a_1\,0\,a_2$ is the matrix $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$.
--
--   Mellin package at the real place: $P\ge 0$ pointwise; $P$ is not almost everywhere zero; for every $\sigma'>x_0$ the function $y\mapsto P(y)|y|^{\sigma'-2}$ is integrable; $x_H<0$; $H_\infty$ is analytic at every real point $\sigma'>x_H$ viewed in $\mathbb{C}$; $H_\infty(0)=0$; and for every $s$ with $\max(x_0,0)<\operatorname{Re}s$,
--   $$H_\infty(s)\cdot\Bigl(\tfrac12\,\pi^{-s}\,\Gamma(s)\int_{\mathbb{R}}P(y)|y|^{s-2}\,dy\Bigr)=1 .$$
--
--   Unramified local data: for $v\notin S$ the image of $\varpi_v$ has valuation $\exp(-1)$, so $\varpi_v$ is a uniformiser; for $v\notin S$ all four of $\|\lambda_v\|,\|\mathrm{om}_v\|,\|\lambda'_v\|,\|\mathrm{om}'_v\|$ are at most $(\#\mathcal{O}/v)^{\kappa}$; the triple product $W_fW_f'F_f$ is invariant under left multiplication by the finite unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); for each $v\notin S$ there is an additive character $\psi_v$ of the completion at $v$, trivial on the valuation ring and nontrivial on $\varpi_v^{-1}$ times the valuation ring (there is $r$ in the valuation ring with $\psi_v(r/\varpi_v)\neq 1$), such that $W_f(\mathtt{finFactor}(n_v(x)g))=\psi_v(x)W_f(\mathtt{finFactor}\,g)$ for all $x$ and $g$, where $n_v(x)$ is the local unipotent matrix embedded at $v$; for $v\notin S$, $W_f\circ\mathtt{finFactor}$ is invariant under right multiplication by the embedded subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $v$ of level the unit ideal, and so is the product $(W_f'F_f)\circ\mathtt{finFactor}$.
--
--   Torus recursion at good places: for $v\notin S$, for every $g$ with trivial component at $v$ and all $m,n\in\mathbb{Z}$, the triple product $W_fW_f'F_f$ evaluated at the finite factor of $g$ times the element of $\mathrm{GL}_2$ at $v$ given by $\mathrm{diag}(\varpi_v^m,1)\cdot(\varpi_v I)^n$ equals the triple product at the finite factor of $g$, multiplied by $0$ unless $0\le m$ and $0\le n$, and in the latter case by
--   $$(\mathrm{om}_v\,\mathrm{om}'_v)^{n}\;\mathtt{heckeRecursionSeq}\,(\#\mathcal{O}/v)\,\lambda_v\,\mathrm{om}_v\,m\;\cdot\;\mathtt{heckeRecursionSeq}\,(\#\mathcal{O}/v)\,\lambda'_v\,\mathrm{om}'_v\,m,$$
--   where `heckeRecursionSeq` $N\,\lambda\,\mathrm{om}$ is the sequence $x_0=1$, $x_1=\lambda/N$, $x_{m+2}=(\lambda x_{m+1}-\mathrm{om}\,x_m)/N$.
--
--   Matching of Euler factors: for every $v\notin S$ and every $X\in\mathbb{C}$, the degree-six polynomial $\mathtt{rsEulerPoly}$ with parameters $\lambda_v/N_v$, $\mathrm{om}_v/N_v$, $\lambda'_v/N_v$, $\mathrm{om}'_v/N_v$ and last parameter $0$ (where $N_v=\#\mathcal{O}/v$), evaluated at $N_vX$, coincides with $\mathtt{rsEulerPoly}$ with parameters $\Theta.a\,v/\Theta.b\,v$, $(\Theta.b\,v)^{-1}$, $\Theta.a\,v$, $\Theta.b\,v$ and last parameter $0$, evaluated at $X$.
--
--   Support and boundedness at the finite places: there exist a compact set $\mathrm{Cpt}$ in `finiteAdelicGL2Subgroup ℚ` and a real $B_0$ such that $\|W_f(g)(W_f'(g)F_f(g))\|\le B_0$ for all $g$, and such that for every $g$ whose component at each $v\notin S$ factors as an element of the range of the local unipotent homomorphism times an element of [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $v$ of level the unit ideal, and for which the triple product at $g$ is nonzero, there are $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h\in\mathrm{Cpt}$ with $ng$ and $h$ having the same component at every $v\in S$.
--
--   Dirichlet-series shape of the finite integral: for every Haar measure $\mu_f$ on `finiteAdelicGL2Subgroup ℚ` and every Haar measure $\mu_{N,f}$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), there exist $A\in\mathbb{N}$, a function $c_f:\mathbb{Z}\to\mathbb{R}$ and a real $B>1$ with $c_f\ge 0$ pointwise and $c_f(n)>0$ for some $n$ with $-A\le n\le A$, such that for all $s\in\mathbb{C}$ the finite Rankin–Selberg integral [`RSCarrier.rsFinIntegral`](def/LanglandsTunnell_RSCarrier.html#L46) $\mu_f\,\mu_{N,f}\,s$, taken with the first argument the restriction of $W_f$ to the set of $g$ whose component at each $v\notin S$ lies in the product of the local unipotent range and the local level-one subgroup, and the second argument the restriction of $W_f'F_f$ to the same set, equals $\sum_{n=-A}^{A}c_f(n)\,B^{-ns}$; here `rsFinIntegral` is the integral of $W(g)F(g)\,\|\det g\|_{\mathbb{A}}^{\,s-1/2}$ against $\mu_f$ with the density attached to the unipotent quotient.
--
--   This is the data-assembly step of the Rankin–Selberg construction over $\mathbb{Q}$: starting from a Hecke eigensystem that is genuinely cusp-realizable in the arithmetic normalisation at a covering centre-cut Siegel window, it produces a complete package of test vectors — an automorphic pair $\varphi,\varphi'$ with opposite central characters, pure-tensor Whittaker functions, a Gaussian Godement section, the archimedean torus profile with its Mellin factor, the unramified torus recursion with matching Euler polynomials, and the finite integral in Dirichlet-series form — together with all side conditions the assembly consumes. It is used by [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), the global Rankin–Selberg integral identity for the Godement–Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat.lean

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
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker
open LanglandsTunnell

theorem AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (WA WA' FA : GL (Fin 2) ℝ → ℂ)
      (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
      (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
      (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
      (P : ℝ → ℝ) (x₀ xH : ℝ) (Hinf : ℂ → ℂ)
      (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
      (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
      (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
      (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ)),
      Continuous φ ∧ Continuous φ' ∧
      IsRapidlyDecreasingOnSiegelSets ℚ φ ∧ IsRapidlyDecreasingOnSiegelSets ℚ φ' ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g) ∧
      IsIdeleClassChar (𝓞 ℚ) ℚ ω ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (centralScalar (𝓞 ℚ) ℚ z * g) = ((ω⁻¹ z : ℂˣ) : ℂ) * φ' g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ a g‖) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' a g‖) ∧
      Φ ∈ schwartzBruhat2 ℚ ∧
      0 < e₁ ∧ e₁ < e₂ ∧ 0 < cS ∧ MeasurableSet D ∧ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤ ∧
      D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
        ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
          {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g)) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g)) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g)) ∧
      (∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
          (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) ∧
      Measurable WA ∧ Measurable WA' ∧ Measurable P ∧
      Measurable Wf ∧ Measurable Wf' ∧ Measurable Ff ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g) ∧
      (∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
        WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ P y) ∧ (¬ ∀ᵐ y : ℝ, P y = 0) ∧
      (∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2))) ∧
      xH < 0 ∧ (∀ σ' : ℝ, xH < σ' → AnalyticAt ℂ Hinf (σ' : ℂ)) ∧ Hinf 0 = 0 ∧
      (∀ s : ℂ, max x₀ 0 < s.re →
        Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ X : ℂ,
        (rsEulerPoly (lam v / (Ideal.absNorm v.asIdeal : ℂ)) (om v / (Ideal.absNorm v.asIdeal : ℂ))
            (lam' v / (Ideal.absNorm v.asIdeal : ℂ)) (om' v / (Ideal.absNorm v.asIdeal : ℂ)) 0).eval
          ((Ideal.absNorm v.asIdeal : ℂ) * X) =
        (rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval X) ∧
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
        ∃ (A : ℕ) (cf : ℤ → ℝ) (B : ℝ), 1 < B ∧ (∀ n, 0 ≤ cf n) ∧ (∃ n, -(A : ℤ) ≤ n ∧ n ≤ A ∧ 0 < cf n) ∧
          ∀ s : ℂ, RSCarrier.rsFinIntegral μf μNFin s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k'}.indicator (fun g => Wf g))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k'}.indicator (fun g => Wf' g * Ff g)) =
            ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)) := by sorry
