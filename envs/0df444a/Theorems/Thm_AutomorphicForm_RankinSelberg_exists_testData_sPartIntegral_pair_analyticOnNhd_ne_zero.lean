-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero
-- name    : AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/4fed51f7-567e-51f8-b2f6-cae1fdc26b72
-- title:
--   Rankin–Selberg test data: bad part analytic, non-zero at centre
-- statement:
--   Setting. Let $K$ be a number field, and let $\alpha \colon (\mathbb{A}_K)^\times \to \mathbb{R}^\times$ be the character obtained from the module character `distribHaarChar` of the adele ring by pushing its $\mathbb{R}_{\ge 0}$-valued character into $\mathbb{R}$ and passing to units, so that $\alpha(z)$ is the idele norm $\lVert z\rVert$. The hypothesis `hα` records that all values $\alpha(z)$ are positive, which is what permits the complex powers $z\mapsto \alpha(z)^{s}$ occurring in `cpowChar`, `etaFst` and `etaSnd` to be formed.
--
--   Window data. Real numbers $c,u,d_1,d_2$ and a finite set $T \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ are given, subject to `_hc` : $0 < c$, `_hd₁` : $0 < d_1$, `_hd` : $d_1 < d_2$, and `_hcov` : the set $D := \bigcup_{x\in T} \mathfrak{S}\cdot x$, where $\mathfrak{S} =$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components have local height $\ge c$ at every infinite place, have $x$-window square $\le u^2$ at every infinite place, and have archimedean determinant norm in $[d_1,d_2]$ at every infinite place, satisfies `CoversModCentre`: every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ can be moved into $D$ by left multiplication by a rational point `globalPoints γ` and right multiplication by a central idelic scalar. Throughout, `pins` denotes `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier package whose measurable structure and measure on $\mathrm{GL}_2(\mathbb{A}_K)$ are the Borel structure and Haar measure, whose region is $D$, whose central subgroup is all of $(\mathbb{A}_K)^\times$, whose level subgroups are $\mathrm{levelOne}(N)\cap\ker(\text{glArch})$, whose Hecke generators are `heckeGen`, and whose additive measure is the additive Haar measure of $\mathbb{A}_K$ conditioned on the adelic box.
--
--   Eigensystems and realizations. Two Hecke eigensystems $\sigma,\tau$ over $K$ with complex values are given (each consisting of a non-zero level ideal and families $a_v,b_v$ indexed by the finite places), together with smooth cusp realizations $R_\sigma$, $R_\tau$ at `pins` of the raw-central rescalings $\sigma$`.toRawCentral`, $\tau$`.toRawCentral` (same level and same $a_v$, with $b_v$ replaced by $b_v/\mathrm{N}(v)$). Such a realization is a function on $\mathrm{GL}_2(\mathbb{A}_K)$ which is somewhere non-zero, has a central character on $(\mathbb{A}_K)^\times$, is a smooth cuspidal automorphic function at `pins` for that central character, is invariant under right translation by the level subgroup at its level, and, outside a finite exceptional set of places, is a Hecke coset eigenfunction with eigenvalue $a_v$ and satisfies the central eigenvalue relation with $b_v/\mathrm{N}(v)$. The hypotheses `_hRσ` and `_hRτ` are `IsGenuineCuspRealizationAt`, i.e. continuity of $R_\sigma$`.toFun` and $R_\tau$`.toFun`.
--
--   Constituent and type data. Archimedean type families `tysσ`, `tysτ` and $\mathbb{C}$-submodules $V_\sigma, V_\tau$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ are given with: `_hVσ`, `_hVτ` : $V_\sigma$, $V_\tau$ are cuspidal constituents at `pins` for the central characters of $R_\sigma$, $R_\tau$, that is, cusp subrepresentations (contained in the $K$-finite cusp submodule, stable under right translation by the finite-adelic subgroup and by the archimedean row-isometry subgroups, and stable under right convolution by factorizable archimedean bi-finite test functions) which are non-zero and minimal among cusp subrepresentations contained in them; `_hRσV`, `_hRτV` : $R_\sigma$`.toFun` lies in $V_\sigma$, is invariant under the level subgroup at $\sigma$`.level`, and lies in the archimedean cut submodule of `tysσ` (the intersection over the infinite places of the spans of the finitely many archimedean types listed there), and symmetrically for $R_\tau$, $\tau$`.level`, `tysτ`. Finally `_hw` : there is a finite set $S_0$ of finite places with $\lVert \sigma.b_v\rVert = \lVert \tau.b_v\rVert$ for all $v \notin S_0$.
--
--   Conclusion. There exist a finite set $S$ of finite places of $K$, functions $f_x, f_y \colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, a character $\nu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$, a family $\varphi \colon \mathbb{C} \to (\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$, real numbers $w, e_1, e_2, d_1', d_2', a$, a set $\mathcal{F} \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ and a finite set `tset` $\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ such that the following hold, where $X :=$ `rightConv K Rτ.toFun fx` and $Y :=$ `rightConv K Rσ.toFun fy` denote the right convolutions $g \mapsto \int R_\tau(gh)f_x(h)\,dh$ and $g\mapsto \int R_\sigma(gh)f_y(h)\,dh$ against Haar measure.
--
--   (1) Good places: for every finite place $v \notin S$, $v$ divides neither $\sigma$`.level` nor $\tau$`.level`, and $v$ lies in neither $R_\sigma$`.exceptionalSet` nor $R_\tau$`.exceptionalSet`.
--
--   (2) Test functions: $f_x$ and $f_y$ are factorizable test functions, i.e. each is a product of a smooth compactly supported function of the archimedean matrix entries with a locally constant compactly supported function of the finite part.
--
--   (3) The character $\nu$ is unitary (all values of modulus one) and is an idele class character (trivial on the principal ideles coming from $K^\times$).
--
--   (4) Central character relation: for every idele $z$, the value of $R_\tau$'s central character at $z$, times the complex conjugate of the value of $R_\sigma$'s central character at $z$, times $\nu(z)$, equals $\lVert z\rVert^{2w}$.
--
--   (5) Induced sections: for every $s\in\mathbb{C}$, $\varphi_s$ is an induced section for the pair `etaFst 1 α hα s` $= \alpha(\cdot)^{s+1/2}$ and `etaSnd ν α hα s` $= \nu(\cdot)\,\alpha(\cdot)^{-(s+1/2)}$; that is, $\varphi_s(bg) = \alpha(b_{11})^{s+1/2}\,\nu(b_{22})\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for all $g$ and all $b$ in the adelic Borel subgroup.
--
--   (6) Regularity of the family: each $\varphi_s$ is archimedean $K$-finite (satisfying `RightTranslatesSpanFinite` for the row-isometry subgroup at every infinite place) and $K_f$-smooth (a smooth vector for right translation by the finite-adelic subgroup); the map $(s,g)\mapsto \varphi_s(g)$ is continuous; and $s \mapsto \varphi_s(g)$ is differentiable on all of $\mathbb{C}$ for each $g$.
--
--   (7) Bruhat summability: for every $s$ with $\operatorname{Re} s > 1/2$ and every $g$, the family $\xi \mapsto \lVert \varphi_s(w_0\,u(\xi)\,g)\rVert$, indexed by $\xi \in K$, is summable, where $w_0 =$ `adelicWeyl` and $u(\xi)$ is the upper unipotent matrix with entry the image of $\xi$ in $\mathbb{A}_K$.
--
--   (8) Sphericality off $S$: for every $s$, every $v \notin S$, every $k_v \in \mathrm{GL}_2(\mathcal{O}_v)$ and every $g$, right multiplication of $g$ by the element of $\mathrm{GL}_2(\mathbb{A}_K)$ supported at $v$ attached to $k_v$ leaves $\varphi_s(g)$ unchanged.
--
--   (9) Behaviour at the centre when $\nu = 1$: if $\nu = 1$ then for every $k$ whose finite part lies in `finiteIntegralGL2` and all of whose archimedean components are row isometries, $\varphi_{1/2}(k)$ has non-negative real part and vanishing imaginary part; and there exists at least one such $k$ with $\varphi_{1/2}(k) \ne 0$.
--
--   (10) Slab and fundamental domain: $0 < e_1 < e_2$; $\mathcal{F}$ is measurable and contained in $\{g : \lVert\det g\rVert \in [e_1,e_2]\}$; $\mathcal{F}$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on Haar measure restricted to that slab; $0 < d_1'$; and $\mathcal{F} \subseteq \bigcup_{t \in \text{tset}}$ `centreCutSiegelSet K c u d₁' d₂'` $\cdot t$.
--
--   (11) Properties of $X$ (and, in an identical list with $\sigma$, $R_\sigma$, $f_y$ in place of $\tau$, $R_\tau$, $f_x$, of $Y$): $X$ is continuous and $K_f$-smooth; $X$ is cuspidal, i.e. its constant term along the unipotent embedding $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, computed against the additive Haar measure of $\mathbb{A}_K$ conditioned on the adelic box, vanishes at every $g$; $X$ is left invariant under `globalPoints γ` for every $\gamma \in \mathrm{GL}_2(K)$; $X(z\cdot g) = \omega_\tau(z)X(g)$ for every central idelic scalar, $\omega_\tau$ being the central character of $R_\tau$; $\lVert\omega_\tau(z)\rVert = \lVert z\rVert^{w}$ for every idele $z$; the Whittaker coefficient of $X$ at $\alpha = 0$, taken at `pins` with the standard additive character, vanishes at every $g$; for every $g$ the family of norms of the Whittaker coefficients of $X$ at $b$, indexed by $b \in K$, is summable; for $v \notin S$, $X$ is invariant under right multiplication by the elements of $\mathrm{GL}_2(\mathcal{O}_v)$ placed at $v$; for $v \notin S$, $X$ is a Hecke coset eigenfunction at $v$ for the subgroup $\mathrm{levelOne}(\tau.\text{level})\cap\ker(\text{glArch})$ and the generator `heckeGen v`, with eigenvalue $\tau$`.toRawCentral.a v` (by definition $a_v(\tau)$); for $v \notin S$ and every $g$ for which the $v$-valuation of $\det g$ equals the square of the maximum of the $v$-valuations of the entries $g_{10}$ and $g_{11}$, the first Whittaker coefficient of $X$ vanishes at $(\text{heckeGen}\,v)^{-m}g$ for all $m > 0$; for each $t \in$ `tset` and each $N \in \mathbb{N}$, the function $g \mapsto \lVert X(g)\rVert^2\,(1+\text{archHeight}(g t^{-1}))^N\,\lVert\det g\rVert^{-w}$ is integrable on $\mathcal{F} \cap \mathfrak{S}(c,u,d_1',d_2')\cdot t$; and for every $s$ with $\operatorname{Re} s > 1/2$, the function $g \mapsto \lVert X(g)\rVert^2\bigl(\lVert\varphi_s(g)\rVert + \sum_{\xi\in K}\lVert\varphi_s(w_0u(\xi)g)\rVert\bigr)\lVert\det g\rVert^{-w}$ is integrable on $\mathcal{F}$.
--
--   (12) Mixed integrability: for each $t \in$ `tset` and each $N \in \mathbb{N}$, the function $g \mapsto \lVert X(g)\rVert\,\lVert Y(g)\rVert\,(1+\text{archHeight}(gt^{-1}))^N\lVert\det g\rVert^{-w}$ is integrable on $\mathcal{F}\cap\mathfrak{S}(c,u,d_1',d_2')\cdot t$.
--
--   (13) Two unfolding identities for the Petersson integral $P(x_1,x_2) := \int_{\mathcal{F}} x_1(g)\overline{x_2(g)}\lVert\det g\rVert^{-w}\,dg$: first, $P(X,Y) = \int f_x(x_1)\,P\bigl(h\mapsto R_\tau(hx_1),\,Y\bigr)\,dx_1$; second, for every $x_1$, $P\bigl(h\mapsto R_\tau(hx_1),\,Y\bigr) = \int \overline{f_y(x_2)}\,P\bigl(h\mapsto R_\tau(hx_1),\,h\mapsto R_\sigma(hx_2)\bigr)\,dx_2$.
--
--   (14) Polynomial bounds: there is a real $\kappa$ such that for every $v \notin S$ one has $\lVert \tau.a_v\rVert \le \mathrm{N}(v)^{\kappa}$, $\lVert \tau.b_v/\mathrm{N}(v)\rVert \le \mathrm{N}(v)^{\kappa}$, and the same two bounds with $\sigma$ in place of $\tau$, $\mathrm{N}(v)$ being the absolute norm of $v$.
--
--   (15) Hecke recursion at the good places: for every $v \notin S$, every $g$ for which the $v$-valuation of $\det g$ equals the square of the maximum of the $v$-valuations of $g_{10}$ and $g_{11}$, and every $m \in \mathbb{N}$, the product of the first Whittaker coefficient of $X$ at $(\text{heckeGen}\,v)^m g$ with the conjugate of the first Whittaker coefficient of $Y$ at $(\text{heckeGen}\,v)^m g$ equals $\text{heckeRecursionSeq}\bigl(\mathrm{N}(v),\tau.a_v,\tau.b_v/\mathrm{N}(v)\bigr)(m)$ times $\text{heckeRecursionSeq}\bigl(\mathrm{N}(v),\overline{\sigma.a_v},\overline{\sigma.b_v/\mathrm{N}(v)}\bigr)(m)$ times the product of the first Whittaker coefficient of $X$ at $g$ with the conjugate of the first Whittaker coefficient of $Y$ at $g$.
--
--   (16) The bad-place part: $a < 1/2$; the function $s \mapsto$ `sPartIntegral K S pins` (standard additive character) $X\ Y\ \varphi_s\ w\ e_1\ e_2$ — the integral over those classes of the rational centre–unipotent quotient whose chosen representatives lie in `shellZeroOutside K S`, of the associated quotient integrand — is analytic on a neighbourhood of every point of $\{s : a < \operatorname{Re} s\}$; and its value at $s = 1/2$, i.e. with $\varphi_{1/2}$ inserted, is non-zero.
--
--   This is the data-selection step of the Rankin–Selberg construction for a pair of $\mathrm{GL}_2$ cusp realizations: it produces simultaneously the test vectors, the unitary idele class character $\nu$ matching the two central characters, the flat family of Eisenstein sections $\varphi_s$, the fundamental domain inside a norm slab covered by centre-cut Siegel sets, all the convergence and Whittaker data that the unfolding and the Euler factorisation consume, and — the point of the non-vanishing clause — a choice for which the part of the integral over the places in $S$ is holomorphic past the centre and does not vanish there. It feeds the analytic continuation and Euler product statement [`AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero.lean

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

theorem AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero
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
      (w e₁ e₂ d₁' d₂' a : ℝ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (tset : Finset (AdelicGL2 (𝓞 K) K)),

      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ¬ v.asIdeal ∣ σ.level ∧ ¬ v.asIdeal ∣ τ.level ∧ v ∉ Rσ.exceptionalSet ∧ v ∉ Rτ.exceptionalSet) ∧

      IsFactorizableTestFn K fx ∧ IsFactorizableTestFn K fy ∧
      IsUnitaryChar (𝓞 K) K ν ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (starRingEnd ℂ) ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ)) ∧

      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s)) ∧
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
      (ν = 1 →
        (∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0) ∧
        (∃ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K ∧
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) ∧
            φ (1 / 2) k ≠ 0)) ∧

      0 < e₁ ∧ e₁ < e₂ ∧ MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      0 < d₁' ∧ 𝓕 ⊆ (⋃ t ∈ tset, (· * t) '' centreCutSiegelSet K c u d₁' d₂') ∧

      Continuous (rightConv K Rτ.toFun fx) ∧ IsKfSmooth K (rightConv K Rτ.toFun fx) ∧
      @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
        unipotentGL2 (rightConv K Rτ.toFun fx) ∧
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightConv K Rτ.toFun fx (globalPoints (𝓞 K) K γ * g) = rightConv K Rτ.toFun fx g) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        rightConv K Rτ.toFun fx (centralScalar (𝓞 K) K z * g) =
          ((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * rightConv K Rτ.toFun fx g) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ‖((Rτ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w) ∧
      (∀ g, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) 0 g = 0) ∧
      (∀ g, Summable fun b : K => ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) b g‖) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          rightConv K Rτ.toFun fx (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = rightConv K Rτ.toFun fx g) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K τ.level ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) v (rightConv K Rτ.toFun fx) (τ.toRawCentral.a v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) ∧
      (∀ t ∈ tset, ∀ N : ℕ, IntegrableOn
        (fun g => ‖rightConv K Rτ.toFun fx g‖ ^ 2 *
          (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
        (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun g => ‖rightConv K Rτ.toFun fx g‖ ^ 2 *
          (‖φ s g‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
          (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      Continuous (rightConv K Rσ.toFun fy) ∧ IsKfSmooth K (rightConv K Rσ.toFun fy) ∧
      @IsCuspidalFn _ (adeleBorel (𝓞 K) K) _ _
        (@ProbabilityTheory.cond _ (adeleBorel (𝓞 K) K) (adelicAddHaar (𝓞 K) K) (adelicBox K))
        unipotentGL2 (rightConv K Rσ.toFun fy) ∧
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightConv K Rσ.toFun fy (globalPoints (𝓞 K) K γ * g) = rightConv K Rσ.toFun fy g) ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        rightConv K Rσ.toFun fy (centralScalar (𝓞 K) K z * g) =
          ((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * rightConv K Rσ.toFun fy g) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ‖((Rσ.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w) ∧
      (∀ g, whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rσ.toFun fy) 0 g = 0) ∧
      (∀ g, Summable fun b : K => ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rσ.toFun fy) b g‖) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          rightConv K Rσ.toFun fy (g * UnramifiedWhittaker.placeEmbed K v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = rightConv K Rσ.toFun fy g) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K σ.level ⊓ finiteAdelicGL2Subgroup K)
          (heckeGen (𝓞 K) K v) v (rightConv K Rσ.toFun fy) (σ.toRawCentral.a v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rσ.toFun fy) 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) ∧
      (∀ t ∈ tset, ∀ N : ℕ, IntegrableOn
        (fun g => ‖rightConv K Rσ.toFun fy g‖ ^ 2 *
          (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
        (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → IntegrableOn (fun g => ‖rightConv K Rσ.toFun fy g‖ ^ 2 *
          (‖φ s g‖ + ∑' ξ : K, ‖φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)‖) *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
          (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      (∀ t ∈ tset, ∀ N : ℕ, IntegrableOn
        (fun g => ‖rightConv K Rτ.toFun fx g‖ * ‖rightConv K Rσ.toFun fy g‖ *
          (1 + archHeight K (glArch (𝓞 K) K (g * t⁻¹))) ^ N *
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w))
        (𝓕 ∩ (· * t) '' centreCutSiegelSet K c u d₁' d₂') (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      (peterssonIntegral K w 𝓕 (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) =
        ∫ x₁, fx x₁ * peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * x₁)) (rightConv K Rσ.toFun fy)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      (∀ x₁ : AdelicGL2 (𝓞 K) K,
        peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * x₁)) (rightConv K Rσ.toFun fy) =
          ∫ x₂, (starRingEnd ℂ) (fy x₂) *
            peterssonIntegral K w 𝓕 (fun h => Rτ.toFun (h * x₁)) (fun h => Rσ.toFun (h * x₂))
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧

      (∃ κ : ℝ, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖τ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖τ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖σ.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖σ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) 1
              ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rσ.toFun fy) 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (τ.a v)
              (τ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) m *
            UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) (σ.a v))
              ((starRingEnd ℂ) (σ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))) m *
            (whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) 1
              (g) *
              (starRingEnd ℂ) (whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rσ.toFun fy) 1
              (g)))) ∧

      a < 1 / 2 ∧
      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ s) w e₁ e₂)
        {s : ℂ | a < s.re} ∧
      RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K Rτ.toFun fx) (rightConv K Rσ.toFun fy) (φ (1 / 2)) w e₁ e₂ ≠ 0 := by sorry
