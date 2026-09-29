-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj
-- name    : AutomorphicForm.setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/9ad79bd7-501f-508e-9788-8ff29403fb1d
-- title:
--   Fubini for the Eisenstein kernel on a measurable rectangle
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring (equipped with the Borel $\sigma$-algebra `adeleBorel`), and $\mathrm{GL}_2(\mathbb{A}_K)$ carries the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` for its Borel $\sigma$-algebra. The statement is parametrised by the following data and hypotheses.
--
--   *Truncation and Siegel data.* Reals $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`); a set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$, which occurs in no hypothesis; reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ with $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`), $d_{1K}<d_{2K}$ (`hdK`), and the covering hypothesis `hcovK`: the union $\bigcup_{x\in T_K}(\,\cdot\,x)\bigl(\mathrm{centreCutSiegelSet}\ K\ c_K\ u_K\ d_{1K}\ d_{2K}\bigr)$ satisfies `CoversModCentre`, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,\mathrm{diag}(z,z)$ in that union; the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has local height $\ge c_K$ and $x$-window square $\le u_K^2$, and whose archimedean determinant norm at each infinite place lies in $[d_{1K},d_{2K}]$.
--
--   *Idele-class data.* A measurable space structure on $(\mathbb{A}_K)^\times$ which is Borel, a Haar measure $\nu_{ZK}$ on $(\mathbb{A}_K)^\times$, and a set $\Omega_K$ which is a fundamental domain (`hΩK`) for the range of $K^\times\to(\mathbb{A}_K)^\times$ with respect to $\nu_{ZK}$.
--
--   *Central character, level, types.* A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top\le(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ with $z\mapsto\xi_K(z)$ continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N\subseteq\mathcal{O}_K$ such that every $v$ with $v$ dividing $N$ lies in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place $w$ a number $\mathrm{card}(w)$ of representations of the row-isometry subgroup of $K_w$. Further, $\alpha_m$ denotes the $\mathbb{R}^\times$-valued character of $(\mathbb{A}_K)^\times$ obtained from `distribHaarChar` of $\mathbb{A}_K$ by composing with $\mathbb{R}_{\ge0}\to\mathbb{R}$, and `hαm` asserts that $\alpha_m(x)>0$ for all $x$.
--
--   *Spectral parameters.* A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\mathrm{Hom}((\mathbb{A}_K)^\times,\mathbb{C}^\times)$ subject to: unitarity of each $\mu_e$ and $\nu_e$ (`_hμ`, `_hν`), triviality on principal ideles (`_hμic`, `_hνic`), continuity (`_hμc`, `_hνc`), the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $e,z$ (`_hμν`), and separation (`_hdist`): distinct indices $e\ne e'$ are distinguished by some norm-one idele, i.e. some $z$ in the kernel of `distribHaarChar` with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$.
--
--   *Sections.* Integers $n_E(e)$ and functions $\varphi_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ for $j\in\mathrm{Fin}(n_E(e))$, subject to the following hypotheses, each required for all $e,j$ and all $s$: `_hφE`, $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair $\bigl(\mu_e\cdot\alpha_m^{\,s+1/2},\ \nu_e\cdot\alpha_m^{-(s+1/2)}\bigr)$, i.e. $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK`, archimedean $K$-finiteness at every infinite place; `_hφEf`, $K_f$-smoothness (open stabiliser inside $\ker(\mathrm{glArch})$); `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, for each infinite place $w$ a single finite-dimensional subspace $W$ of functions on $\mathrm{archRowIsometrySubgroup}\,K\,w$ containing all right-translate functions $k\mapsto\varphi_{e,j}(s,gk)$; `_hφEflat`, flatness on the maximal compact subgroup, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k\in\mathrm{adelicMaximalCompact}$; `_hφElev`, right invariance under $\mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$; `_hφEty`, membership in $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$; `_hφEon`, orthonormality at $s=0$ against `maximalCompactHaar`, the integral of $\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}$ being $1$ if $i=j$ and $0$ otherwise; `_hφEspan`, completeness along the imaginary axis: any $\varphi_0$ which is an induced section for $(\mu_e,\nu_e)$ at $s=it$, continuous, archimedean $K$-finite, invariant under the level group and in the archimedean cut submodule lies in the span of the $\varphi_{e,j}(it,\cdot)$; and `_hpairs`, exhaustiveness: any pair $(\mu',\nu')$ of continuous unitary idele-class characters with $\mu'\nu'=\xi_K$ admitting a non-zero section $\varphi_0$ of the above kind at some $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   *Eisenstein continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j),N_E(e,j)$ of $(s,g)$ subject to `_hEE` (nine clauses): $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; and for $\operatorname{Re}s>1/2$ they are given by the Bruhat expansions $E_E(e,j,s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}\bigl(s,\ w\,u(\xi)\,g\bigr)$ and $N_E(e,j,s,g)=\int \varphi_{e,j}(s,w^{-1}u(x)g)\,dx$ against the additive Haar measure on $\mathbb{A}_K$, where $w$ is the adelic Weyl element and $u(x)$ the upper unipotent.
--
--   *Test function.* A function $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which is continuous (`_hf`) with compact support (`_hfc`), factorizable in the sense of `IsFactorizableTestFn` (a product of an archimedean factor coming from a smooth compactly supported function of the archimedean matrix entries with a locally constant compactly supported function of the finite part), bi-invariant under $\mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, and archimedean bi-finite of type $\mathrm{tys}_K$, i.e. $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule and $f$ lies in the dual cut submodule.
--
--   *Rectangle.* A compact set $C$, and measurable sets $A\subseteq C$ and $B\subseteq C$.
--
--   Write $\mu_{\alpha\beta}$ for the restriction of `adelicGLHaar (Fin 2) (𝓞 K) K` to the canonical truncation domain $\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$, and put
--   $$a_{e,i,j}(t)=\int_{\mathrm{adelicMaximalCompact}} \bigl(\mathrm{rightConv}\,K\,\varphi_{e,j}(it,\cdot)\,f\bigr)(k)\ \overline{\varphi_{e,i}(it,k)}\ d\,\mathrm{maximalCompactHaar},$$
--   where $(\mathrm{rightConv}\,K\,\varphi\,f)(g)=\int_{\mathrm{GL}_2(\mathbb{A}_K)}\varphi(gx)f(x)\,d\,\mathrm{adelicGLHaar}$.
--
--   The conclusion is the single identity
--   $$\int_{A\times B}\ \sum_{e\in\iota_E}^{\prime}\int_{\mathbb{R}}\sum_{i,j}a_{e,i,j}(t)\,E_E(e,i,it,p_1)\,\overline{E_E(e,j,it,p_2)}\ dt\ d(\mu_{\alpha\beta}\otimes\mu_{\alpha\beta})(p)$$
--   $$=\sum_{e\in\iota_E}^{\prime}\int_{\mathbb{R}}\sum_{i,j}a_{e,i,j}(t)\left(\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta}\mathbf 1_B(g)\,\overline{E_E(e,j,it,g)}\,dg\right)\overline{\left(\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta}\mathbf 1_A(g)\,\overline{E_E(e,i,it,g)}\,dg\right)}dt,$$
--   where the sums over $e$ are the $\mathbb{C}$-valued infinite sums over the countable index type, the inner finite sums run over $i,j\in\mathrm{Fin}(n_E(e))$, the indicator functions take the value $1\in\mathbb{C}$ on $B$ respectively $A$, and the integrals over the truncation domain on the right-hand side are taken against `adelicGLHaar (Fin 2) (𝓞 K) K`.
--
--   This is the Fubini step in the continuous-spectrum (Eisenstein) part of the adelic trace formula for $\mathrm{GL}_2$: the double integral of the Eisenstein kernel over a measurable rectangle $A\times B$ inside a compact set is evaluated term by term, as a spectral sum and integral of the coefficients $a_{e,i,j}(t)$ multiplied by the pairings of the indicators of $B$ and $A$ against the truncated Eisenstein series. It is used in [`AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation), where the continuous part of the kernel is identified with the operator attached to the test function $f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
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
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation_mul_conj_eq_tsum_integral_sum_mul_setIntegral_indicator_mul_conj
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (A : Set (AdelicGL2 (𝓞 K) K)) (_hA : A ⊆ C) (_hAm : MeasurableSet A)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B),
    ∫ p in A ×ˢ B, (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) p.1 * conj (EE e j ((t : ℂ) * Complex.I) p.2))) ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) =
      ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                B.indicator (fun _ => (1 : ℂ)) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                A.indicator (fun _ => (1 : ℂ)) g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by sorry
