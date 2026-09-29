-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_self_analyticOnNhd_re_pos
-- name    : AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/501d9cbc-323d-56f4-93d4-780f3d2ca8bb
-- title:
--   Rankin–Selberg test data: bad-place part analytic and positive past 1/2
-- statement:
--   Let $K$ be a number field. Write $\alpha$ for the monoid homomorphism $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the module character `distribHaarChar (AdeleRing (𝓞 K) K)` by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units; thus $\alpha$ is the idele norm, and [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19) is its underlying real-valued function. The statement is quantified over a proof `hα` that $\alpha(t) > 0$ for every $t$.
--
--   The data fixed are: reals $c, u, d_1, d_2$ and a finite set $T \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, subject to $0 < c$, $0 < d_1$, $d_1 < d_2$ (hypotheses `_hc`, `_hd₁`, `_hd`); the window
--   $$W \;=\; \bigcup_{x \in T} \{g x : g \in \Sigma\},\qquad \Sigma = \mathtt{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2,$$
--   where $\Sigma$ consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height $\ge c$ and $x$-window square $\le u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; the hypothesis `_hcov` states `CoversModCentre K W`, i.e. for every $g$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g \cdot z \in W$ (global point on the left, central scalar on the right). Throughout, $P$ denotes the production pins `productionPinsOf K W (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the set $W$, the full group $\top$ of ideles as central subgroup $Z$, the level subgroups $U(N) = \mathtt{levelOne}(N) \cap \ker(\mathtt{glArch})$, the Hecke elements $\mathtt{heckeGen}(v)$, the Borel structure on $\mathbb{A}_K$ and the additive Haar measure of $\mathbb{A}_K$ conditioned on the box `adelicBox K`.
--
--   Further data: a Hecke eigensystem $\Theta$ over $K$ with complex values (a nonzero level ideal and families $a_v, b_v$); a smooth cusp realisation $R$ at the pins $P$ for `Θ.toRawCentral`, the eigensystem with the same level and the same $a_v$ but with $b_v$ replaced by $b_v/\mathrm{N}(v)$ — so $R$ carries a function `R.toFun`, a point where it is nonzero, a central character `R.centralChar` on $Z = \top$, the smooth-cusp-automorphy property, invariance under $U(\Theta.\mathtt{level})$ on the right, a finite exceptional set `R.exceptionalSet`, Hecke coset eigenfunction equations with eigenvalues $a_v$ and central eigenvalue equations with $b_v/\mathrm{N}(v)$ away from the exceptional set; the hypothesis `_hR` that `R.toFun` is continuous (`IsGenuineCuspRealizationAt`); an archimedean type family `tys` (a finite multiplicity and a finite list of representations of the row-isometry subgroup at each infinite place); and a $\mathbb{C}$-submodule $V$ of functions $\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ with `_hV` asserting `IsCuspConstituent K P R.centralChar V`, that is, $V$ is a cusp subrepresentation at the pins for the central character `R.centralChar` (contained in the $K$-finite cusp submodule and stable under right translation by the finite adelic subgroup, by archimedean row isometries, and under right convolution with factorizable test functions of type `tys`), $V \neq \bot$, and $V$ contains no proper nonzero cusp subrepresentation. The hypothesis `_hRV` places `R.toFun` in $V \sqcap \mathtt{levelInvariantSubmodule}\,K\,P\,\Theta.\mathtt{level} \sqcap \mathtt{archCutSubmodule}\,K\,\mathtt{tys}$, i.e. `R.toFun` lies in $V$, satisfies $\varphi(gu) = \varphi(g)$ for all $u \in U(\Theta.\mathtt{level})$, and lies in $\bigsqcap_{w} \bigsqcup_i$ of the archimedean type submodules attached to `tys`.
--
--   The conclusion asserts the existence of a finite set $S$ of finite places of $K$, functions $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ and $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ (written $\varphi_s$), reals $w, e_1, e_2, d_1', d_2', a$, a set $\mathcal{F} \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ and a finite set $\mathtt{tset} \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, with the following properties. Write $x = \mathtt{rightConv}\,K\,R.\mathtt{toFun}\,f$, so $x(g) = \int R.\mathtt{toFun}(g y) f(y)\,dy$ against adelic Haar measure, and write $W_\beta(\cdot) = \mathtt{whittakerCoefficient}\,K\,P\,\psi_K\,x\,\beta\,(\cdot)$ for $\beta \in K$, where $\psi_K$ is [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) and the integration is over $\mathbb{A}_K$ against the Haar measure conditioned on `adelicBox K`.
--
--   First, for every finite place $v \notin S$, $v$ does not divide $\Theta.\mathtt{level}$ and $v \notin R.\mathtt{exceptionalSet}$.
--
--   On the test function and the section family: $f$ is a factorizable test function, i.e. $f(g) = f_\infty(\mathtt{glArch}\,g)\,f_{\mathrm{fin}}(\mathtt{glFin}\,g)$ with $f_\infty$ given by a smooth compactly supported function of the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant with compact support. For every $s$, $\varphi_s$ is an induced section for the pair of characters $\mathtt{etaFst}\,1\,\alpha\,h\alpha\,s = \alpha^{s+1/2}$ and $\mathtt{etaSnd}\,1\,\alpha\,h\alpha\,s = \alpha^{-(s+1/2)}$, that is, $\varphi_s(bg) = \alpha(b_{11})^{s+1/2}\,\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for $b$ in the adelic Borel subgroup; every $\varphi_s$ is archimedean $K$-finite and $K_f$-smooth; $(s,g) \mapsto \varphi_s(g)$ is continuous; $s \mapsto \varphi_s(g)$ is differentiable on all of $\mathbb{C}$ for each $g$; for $\mathrm{Re}\,s > 1/2$ and every $g$ the family $\xi \in K \mapsto \lVert \varphi_s(\mathrm{w}\,n(\xi)\,g)\rVert$ is summable, where $\mathrm{w} = \mathtt{adelicWeyl}$ and $n(\xi) = \mathtt{unipotentGL2}$ of the image of $\xi$ in $\mathbb{A}_K$; and for every $s$, every $v \notin S$ and every $k_v \in \mathrm{GL}_2(\mathcal{O}_v)$ one has right invariance $\varphi_s(g\,\iota_v(k_v)) = \varphi_s(g)$, $\iota_v$ being [`UnramifiedWhittaker.placeEmbed`](def/UnramifiedWhittaker_HeckeRecursion.html#L47). At the central point, $\varphi_{1/2}$ takes nonnegative real values on every $k$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at each infinite place is a row isometry (that is, $\mathrm{Re}\,\varphi_{1/2}(k) \ge 0$ and $\mathrm{Im}\,\varphi_{1/2}(k) = 0$), and there is at least one such $k$ with $\varphi_{1/2}(k) \neq 0$.
--
--   On the fundamental domain: $0 < e_1 < e_2$, $\mathcal{F}$ is measurable and contained in the slab $\{g : \lVert \det g\rVert_{\mathbb{A}} \in [e_1,e_2]\}$, and $\mathcal{F}$ is a fundamental domain for the range of $\mathtt{globalPoints}$ acting on that slab with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to the slab; moreover $0 < d_1'$ and $\mathcal{F} \subseteq \bigcup_{t \in \mathtt{tset}} \{g t : g \in \mathtt{centreCutSiegelSet}\,K\,c\,u\,d_1'\,d_2'\}$.
--
--   On the smoothed vector $x$: $x$ is continuous and $K_f$-smooth; $x$ is cuspidal in the sense of `IsCuspidalFn`, i.e. its constant term along `unipotentGL2` against the additive Haar measure of $\mathbb{A}_K$ conditioned on `adelicBox K` vanishes at every point; $x(\gamma g) = x(g)$ for every $\gamma \in \mathrm{GL}_2(K)$ (through `globalPoints`) and every $g$; $x(z g) = R.\mathtt{centralChar}(z)\,x(g)$ for every idele $z$ (viewed in $Z = \top$) and every $g$, the central scalar being `centralScalar`; $\lVert R.\mathtt{centralChar}(z)\rVert = \lVert z\rVert_{\mathbb{A}}^{\,w}$ for every idele $z$; the zeroth Whittaker coefficient $W_0(g)$ vanishes for every $g$, and for every $g$ the family $\beta \in K \mapsto \lVert W_\beta(g)\rVert$ is summable; $x(g\,\iota_v(k_v)) = x(g)$ for $v \notin S$ and $k_v \in \mathrm{GL}_2(\mathcal{O}_v)$; and for every $v \notin S$, $x$ is a Hecke coset eigenfunction at $v$ for the subgroup $\mathtt{levelOne}(\Theta.\mathtt{level}) \cap \ker(\mathtt{glArch})$ and the element $\mathtt{heckeGen}(v)$, with eigenvalue $\mathtt{Θ.toRawCentral.a}\,v$ (equal to $a_v$); that is, there is a system of $\mathrm{N}(v)+1$ coset representatives whose Hecke sum applied to $x$ equals $a_v\,x$.
--
--   On the local Hecke data: there is a real $\kappa$ such that for all $v \notin S$ one has $\lVert a_v\rVert \le \mathrm{N}(v)^{\kappa}$ and $\lVert b_v/\mathrm{N}(v)\rVert \le \mathrm{N}(v)^{\kappa}$, where $\mathrm{N}(v) = \mathtt{Ideal.absNorm}\,v.\mathtt{asIdeal}$. Moreover, for every $v \notin S$ and every $g$ whose bottom row is primitive at $v$ in the sense that $\mathrm{v}(\det g) = \max(\mathrm{v}(g_{10}), \mathrm{v}(g_{11}))^2$ in the value group at $v$, the following hold: for every $m \in \mathbb{N}$,
--   $$\bigl|W_1\bigl(\mathtt{heckeGen}(v)^m g\bigr)\bigr|^2 \;=\; H_m\,\overline{H}_m\,\bigl|W_1(g)\bigr|^2,$$
--   written in Lean as the product of $W_1$ with its complex conjugate, where $H_m = \mathtt{UnramifiedWhittaker.heckeRecursionSeq}\,\mathrm{N}(v)\,a_v\,(b_v/\mathrm{N}(v))\,m$ and $\overline{H}_m$ is the same sequence with $a_v$ and $b_v/\mathrm{N}(v)$ replaced by their conjugates (the sequence defined by $H_0 = 1$, $H_1 = \lambda/N$, $N H_{m+2} = \lambda H_{m+1} - \omega H_m$); and for every $m > 0$, $W_1(\mathtt{heckeGen}(v)^{-m} g) = 0$.
--
--   On integrability and non-degeneracy: for every $t \in \mathtt{tset}$ and every $N \in \mathbb{N}$, the function
--   $$g \mapsto \lVert x(g)\rVert^2\,\bigl(1 + \mathtt{archHeight}\,K(\mathtt{glArch}(g t^{-1}))\bigr)^N\,\lVert \det g\rVert_{\mathbb{A}}^{-w}$$
--   is integrable on $\mathcal{F} \cap \{g t : g \in \mathtt{centreCutSiegelSet}\,K\,c\,u\,d_1'\,d_2'\}$ against adelic Haar measure, `archHeight` being the product over infinite places of the local heights raised to the multiplicity; for every $s$ with $\mathrm{Re}\,s > 1/2$, the function
--   $$g \mapsto \lVert x(g)\rVert^2\Bigl(\lVert \varphi_s(g)\rVert + \sum_{\xi \in K} \lVert \varphi_s(\mathrm{w}\,n(\xi)\,g)\rVert\Bigr)\lVert \det g\rVert_{\mathbb{A}}^{-w}$$
--   is integrable on $\mathcal{F}$; and the Petersson integral $\mathtt{peterssonIntegral}\,K\,w\,\mathcal{F}\,x\,x = \int_{\mathcal{F}} x(g)\overline{x(g)}\,\lVert \det g\rVert_{\mathbb{A}}^{-w}$ is nonzero.
--
--   Finally, $a < 1/2$, and the bad-place part
--   $$s \mapsto \mathtt{RankinSelberg.sPartIntegral}\,K\,S\,P\,\psi_K\,x\,x\,(\varphi_s)\,w\,e_1\,e_2,$$
--   the integral of `quotientIntegrand` over the set of classes $q$ in the rational centre–unipotent quotient whose representative lies in $\mathtt{shellZeroOutside}\,K\,S$, taken against `rationalCentreUnipotentQuotientMeasure`, is analytic on a neighbourhood of every point of the half-plane $\{s : a < \mathrm{Re}\,s\}$; and for every real $\sigma > a$ this quantity evaluated at $\varphi_\sigma$ has vanishing imaginary part and strictly positive real part.
--
--   This is the packaging step of the global Rankin–Selberg method for $\mathrm{GL}_2$ over a number field: starting from a merely continuous cusp realisation of a Hecke eigensystem inside a single cuspidal constituent, it produces a smoothed vector, an entire family of flat induced sections, a slab fundamental domain with a Siegel cover, all the equivariance, Whittaker and integrability properties that the unfolding and Euler factorisation consume, together with holomorphy past $s = 1/2$ and positivity of the part of the integral attached to the places of $S$, the archimedean places, the centre and the slab. It is used by [`AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self), where the Euler product in the unramified places is matched against the Petersson norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_self_analyticOnNhd_re_pos.lean

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
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
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
      (tys : AutomorphicForm.ArchTypeFamily K)
      (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hV : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
      (_hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : AdelicGL2 (𝓞 K) K → ℂ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (w e₁ e₂ d₁' d₂' a : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (tset : Finset (AdelicGL2 (𝓞 K) K)),

      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧

      IsFactorizableTestFn K f ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧ (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), 1 / 2 < s.re →
        Summable fun ξ : K => ‖φ s (adelicWeyl (𝓞 K) K * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) ∧
      (∀ (s : ℂ) (v : HeightOneSpectrum (𝓞 K)), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          φ s (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ s g) ∧

      (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0) ∧
      (∃ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) ∧
          φ (1 / 2) k ≠ 0) ∧

      0 < e₁ ∧ e₁ < e₂ ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      0 < d₁' ∧ 𝓕 ⊆ (⋃ t ∈ tset, (· * t) '' centreCutSiegelSet K c u d₁' d₂') ∧

      Continuous (rightConv K R.toFun f) ∧ IsKfSmooth K (rightConv K R.toFun f) ∧
      @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
        unipotentGL2 (rightConv K R.toFun f) ∧
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightConv K R.toFun f (globalPoints (𝓞 K) K γ * g) = rightConv K R.toFun f g) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        rightConv K R.toFun f (centralScalar (𝓞 K) K z * g) =
          ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * rightConv K R.toFun f g) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ‖((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w) ∧
      (∀ g, whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 0 g = 0) ∧
      (∀ g, Summable fun b : K => ‖whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) b g‖) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          rightConv K R.toFun f (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = rightConv K R.toFun f g) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) v (rightConv K R.toFun f) (Θ.toRawCentral.a v)) ∧

      (∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖Θ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
              ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ.a v)
              (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) (Θ.a v))
              ((starRingEnd ℂ) (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))) m *
            (whittakerCoefficient K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                  (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                  (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                  (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                  (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 g))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) ∧

      (∀ t ∈ tset, ∀ N : ℕ, IntegrableOn
        (fun g => ‖rightConv K R.toFun f g‖ * ‖rightConv K R.toFun f g‖ *
          (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
        (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      (∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun g => ‖rightConv K R.toFun f g‖ ^ 2 *
          (‖φ s g‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
          (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      peterssonIntegral K w 𝓕 (rightConv K R.toFun f) (rightConv K R.toFun f) ≠ 0 ∧

      a < 1 / 2 ∧
      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂)
        {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ →
        (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).im = 0 ∧
        0 < (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).re) := by sorry
