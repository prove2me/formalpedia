-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exports_rightConv_sum_translate_of_isCuspConstituent
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exports_rightConv_sum_translate_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b401b212-70ef-5595-96ad-ff5d3d67cacb
-- title:
--   Export package for translates of a smoothed cuspidal realisation
-- statement:
--   Let $K$ be a number field and write $G=\mathrm{GL}_2(\mathbb A_K)$ for `AdelicGL2 (𝓞 K) K`.
--
--   **Window data.** Real numbers $c,u,d_1,d_2$ and a finite set $T\subseteq G$ are given, with $0<c$, $0<d_1$ and $d_1<d_2$. Put $\mathfrak S=\mathfrak S(c,u,d_1,d_2)=$ `centreCutSiegelSet K c u d₁ d₂`, the set of $g\in G$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K`, whose archimedean component at every infinite place $w$ has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and for which `archDetNorm w g` lies in $[d_1,d_2]$ for every $w$; and let $D=\bigcup_{t\in T}\mathfrak S\,t$ be the corresponding window. The hypothesis `_hcov` is `CoversModCentre K D`: for every $g\in G$ there are $\gamma\in\mathrm{GL}_2(K)$ and a unit idele $z$ with $\mathrm{globalPoints}(\gamma)\,g\,\mathrm{centralScalar}(z)\in D$. Throughout, the carrier pins are $P=$ `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel $\sigma$-algebra and Haar measure on $G$, the window $D$, the full central subgroup $Z=\top$ of $(\mathbb A_K)^\times$, the level subgroups $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\varpi_v=$ `heckeGen (𝓞 K) K v`, and on the adele ring the Borel $\sigma$-algebra together with the additive Haar measure conditioned on the box `adelicBox K`.
--
--   **Eigensystem and realisation.** $\Theta$ is a Hecke eigensystem over $K$ with values in $\mathbb C$ (a nonzero level ideal $\Theta.\mathrm{level}$ and families $a_v,b_v$ indexed by the finite places), and $\Theta.\mathrm{toRawCentral}$ is the eigensystem with the same level and the same $a$, and with $b_v$ replaced by $b_v/N(v)$, where $N(v)=$ `Ideal.absNorm v.asIdeal`. Further, $R$ is a `SmoothCuspRealizationAt K P Θ.toRawCentral`: a function $R.\mathrm{toFun}$ on $G$, not identically zero, with a central character $R.\mathrm{centralChar}$ on $Z=\top$, which is a smooth cusp automorphic function at $P$ for that character, is invariant under right multiplication by $U(\Theta.\mathrm{level})$, and, for $v$ outside a finite exceptional set $R.\mathrm{exceptionalSet}$, is a Hecke coset eigenfunction at $v$ with eigenvalue $a_v$ and satisfies the central eigenvalue relation with $b_v/N(v)$. The hypothesis `_hR` is `IsGenuineCuspRealizationAt`, i.e. continuity of $R.\mathrm{toFun}$; `_hRlev` states again that $R.\mathrm{toFun}(gk)=R.\mathrm{toFun}(g)$ for all $g$ and all $k\in\mathrm{levelOne}(\Theta.\mathrm{level})\cap\mathrm{finiteAdelicGL2Subgroup}$.
--
--   **Test function and places.** $f:G\to\mathbb C$ is a factorizable test function (`_hfT`): $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ given by a $C^\infty$ function of the archimedean matrix entries and compactly supported, and $f_{\mathrm{fin}}$ locally constant with compact support. Finite sets $S,S_f,S_\psi$ of finite places are given with $S_f\subseteq S$ and $S_\psi\subseteq S$. The support hypothesis `_hfsupp` requires, for every $z$ with $f(z)\neq 0$: the $v$-component of the finite part of $z$ lies in `localIntegralSet K v` (that matrix and its inverse have entries in $\mathcal O_v$) for every $v\notin S_f$; and $z=z_1z_2$ with $z_2\in\mathrm{levelOne}(\Theta.\mathrm{level})\cap\mathrm{finiteAdelicGL2Subgroup}$ and $z_1$ commuting with [`UnramifiedWhittaker.placeEmbed K v xv`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) for every $v\notin S_f$ and every $x_v\in\mathrm{GL}_2(K_v)$. The hypothesis `_hS` requires, for $v\notin S$, that $v$ does not divide $\Theta.\mathrm{level}$ and that $v\notin R.\mathrm{exceptionalSet}$; `_hSψ0` requires that the local component `psiLocal K v` of the standard additive character have `addCharLevel` equal to $0$ for every $v\notin S_\psi$.
--
--   **Constituent.** $V$ is a $\mathbb C$-submodule of the functions $G\to\mathbb C$, and `_hV` is `IsCuspConstituent K P R.centralChar V`: $V$ is contained in `cuspKFiniteSubmodule K P R.centralChar`, is stable under right translation by elements of `finiteAdelicGL2Subgroup K` and by the inclusions of the row-isometry subgroups at the infinite places, and is stable under right convolution $\varphi\mapsto\mathrm{rightConv}\,\varphi\,f'$ by factorizable, archimedeanly bi-finite test functions $f'$; moreover $V\neq\bot$ and every submodule $W$ with these three stability properties and $W\le V$ equals $\bot$ or $V$. The hypothesis `_hx₀V` states that $\mathrm{rightConv}\,K\,R.\mathrm{toFun}\,f$, the function $g\mapsto\int_G R.\mathrm{toFun}(gy)f(y)\,dy$ for the Haar measure on $G$, lies in $V$.
--
--   **Fundamental domain and translate family.** A real number $w$ is given, together with a measurable set $\mathcal F\subseteq\{g:\ \mathrm{ideleNorm}(\det g)\in[1,2]\}$ which is a fundamental domain for the range of $\mathrm{globalPoints}$ acting on $G$, for the Haar measure restricted to that slab; reals $d_1',d_2'$ with $0<d_1'$; a natural number $r$, elements $h_i\in G$ and scalars $c_i\in\mathbb C$ for $i\in\mathrm{Fin}\,r$ such that $\mathrm{glArch}(h_i)=1$ for all $i$ (`_hharch`) and each $h_i$ commutes with [`UnramifiedWhittaker.placeEmbed K v xv`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) for every $v\notin S$ and every $x_v\in\mathrm{GL}_2(K_v)$ (`_hhcomm`); and finally a function $x:G\to\mathbb C$ with
--   $$x(g)=\sum_i c_i\,(\mathrm{rightConv}\,K\,R.\mathrm{toFun}\,f)(g\,h_i)\qquad\text{for all }g .$$
--
--   **Conclusion.** The following fourteen assertions hold.
--
--   (1) $x\in V$.
--
--   (2) The function $z\mapsto\sum_i c_i\,f(h_i^{-1}z)$ is again a factorizable test function in the above sense.
--
--   (3) $x$ is continuous.
--
--   (4) `IsSmoothCuspAutomorphicFnAt K P R.centralChar x`: $x$ is a cusp automorphic function at the pins $P$ for the character $R.\mathrm{centralChar}$ (automorphic at $P$ and cuspidal for the unipotent $\mathrm{unipotentGL2}$ and the measure of $P$ on the adele ring), and $x$ is a smooth vector for right translation by `finiteAdelicGL2Subgroup K`.
--
--   (5) $x(\mathrm{globalPoints}(\gamma)\,g)=x(g)$ for every $\gamma\in\mathrm{GL}_2(K)$ and every $g\in G$.
--
--   (6) $x(\mathrm{centralScalar}(z)\,g)=R.\mathrm{centralChar}(z)\,x(g)$ for every unit idele $z$ and every $g$, the character being evaluated on $z$ viewed in $Z=\top$.
--
--   (7) The Whittaker coefficient of $x$ at $\alpha=0$ for the standard additive character [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) and the pins $P$ vanishes at every $g$; that is, $\int \,x(\mathrm{unipotentGL2}(t)\,g)\,dt=0$ for the conditioned additive measure of $P$.
--
--   (8) For every $\alpha'\in K$ and every $g$, the integrand defining the Whittaker coefficient of $x$ at $\alpha'$ (for `stdAddChar K` and $P$) is integrable.
--
--   (9) $x(\mathrm{unipotentGL2}(\beta+u')\,h')=x(\mathrm{unipotentGL2}(u')\,h')$ for every $\beta\in K$ (mapped into $\mathbb A_K$), every $u'\in\mathbb A_K$ and every $h'\in G$.
--
--   (10) For every $g$, the family of norms of the Whittaker coefficients of $x$, indexed by $b\in K$, is summable.
--
--   (11) For every $v\notin S$: $x(g\cdot\mathrm{placeEmbed}\,K\,v\,(k_v))=x(g)$ for every $k_v\in\mathrm{GL}_2(\mathcal O_v)$ (mapped into $\mathrm{GL}_2(K_v)$) and every $g$; and `IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v)` holds, i.e. there are $N(v)+1$ representatives forming a Hecke coset system for that subgroup and the generator $\varpi_v$ such that $\sum_i x(g\,\mathrm{rep}_i)=a_v\,x(g)$ for all $g$.
--
--   (12) $x(gk)=x(g)$ for every $g$ and every $k\in\mathrm{maximalCompactAway}\,K\,S$, the subgroup of elements whose finite part lies in `finiteIntegralGL2 (𝓞 K) K` and whose archimedean components are row isometries, which lie in the kernel of $\mathrm{glArch}$ and whose component at each $v\in S$ is trivial.
--
--   (13) For every $t\in G$ and every $N\in\mathbb N$, the function
--   $$g\mapsto \|x(g)\|^2\,\bigl(1+\mathrm{archHeight}\,K(\mathrm{glArch}(g t^{-1}))\bigr)^{N}\,\mathrm{ideleNorm}(\det g)^{-w}$$
--   is integrable on $\mathcal F\cap \mathfrak S(c,u,d_1',d_2')\,t$ for the Haar measure on $G$ (the square appearing in the Lean as the product $\|x(g)\|\cdot\|x(g)\|$).
--
--   (14) For every $v\notin S$ and every $g$ satisfying the shell condition that the $v$-adic valuation of $\det g$ equal the square of the maximum of the $v$-adic valuations of the two entries of the bottom row of $g$: writing $W_1(\cdot)$ for the Whittaker coefficient of $x$ at $\alpha=1$ for `stdAddChar K` and $P$, and $u_m(\,\cdot\,)$ for [`UnramifiedWhittaker.heckeRecursionSeq`](def/UnramifiedWhittaker_HeckeRecursion.html#L11) (the sequence $u_0=1$, $u_1=\lambda/N$, $u_{m+2}=(\lambda u_{m+1}-\omega u_m)/N$),
--   $$W_1(\varpi_v^{m}g)\,\overline{W_1(\varpi_v^{m}g)}=u_m\bigl(N(v),a_v,b_v/N(v)\bigr)\,u_m\bigl(N(v),\overline{a_v},\overline{b_v/N(v)}\bigr)\cdot W_1(g)\,\overline{W_1(g)}$$
--   for every $m\in\mathbb N$, and $W_1(\varpi_v^{-m}g)=0$ for every $m>0$.
--
--   This is a packaging result: it collects, for a finite linear combination $x$ of right translates of the smoothed vector $R*f$ lying in a cuspidal constituent $V$, the membership, regularity, automorphy, central-character, Whittaker (vanishing constant term, integrability, absolute summability, $K$-periodicity), sphericity and Hecke-eigenvalue statements off $S$, the decay estimate on Siegel pieces of a fundamental domain, and the local recursion for the absolute squares of the first Whittaker coefficient along powers of the Hecke generator. It is used in the Rankin–Selberg step [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero), where such a family supplies the test vectors whose zeta integral is shown to be non-vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exports_rightConv_sum_translate_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.SmoothCuspRealizationAt.exports_rightConv_sum_translate_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (_hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (_hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (_hSf : Sf ⊆ S) (_hSψ : Sψ ⊆ S)
    (_hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (_hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (_hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (_hV : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
    (_hx₀V : rightConv K R.toFun f ∈ V)
    (w : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (_h𝓕m : MeasurableSet 𝓕)
    (_h𝓕s : 𝓕 ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2})
    (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2}))
    (d₁' d₂' : ℝ) (_hd₁' : 0 < d₁')
    (r : ℕ) (h : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (_hharch : ∀ i, glArch (𝓞 K) K (h i) = 1)
    (_hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i)) :
    x ∈ V ∧
    IsFactorizableTestFn K (fun z => ∑ i, cs i * f ((h i)⁻¹ * z)) ∧
    Continuous x ∧
    IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar x ∧
    (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g) ∧
    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 0 g = 0) ∧
    (∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g) ∧
    (∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh)) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, Summable (fun b : K => ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x b g‖)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v)) ∧
    (∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g) ∧
    (∀ (t : AdelicGL2 (𝓞 K) K) (N : ℕ), IntegrableOn
      (fun g => ‖x g‖ * ‖x g‖ * (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
      (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
      (∀ m : ℕ,
        whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ.toRawCentral.a v) (Θ.toRawCentral.b v) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
              ((starRingEnd ℂ) (Θ.toRawCentral.a v)) ((starRingEnd ℂ) (Θ.toRawCentral.b v)) m *
            (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g))) ∧
      (∀ m : ℕ, 0 < m → whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0)) := by sorry
