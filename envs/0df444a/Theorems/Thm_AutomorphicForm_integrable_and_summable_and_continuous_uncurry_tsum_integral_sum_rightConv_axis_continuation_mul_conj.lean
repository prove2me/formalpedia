-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_summable_and_continuous_uncurry_tsum_integral_sum_rightConv_axis_continuation_mul_conj
-- name    : AutomorphicForm.integrable_and_summable_and_continuous_uncurry_tsum_integral_sum_rightConv_axis_continuation_mul_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9d24ad6d-2b72-52a2-bfb6-7daec6aa5521
-- title:
--   Eisenstein kernel: integrability, joint continuity, automorphy
-- statement:
--   Fix a number field $K$, reals $\alpha,\beta$ with $0<\alpha<\beta$, a set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`), reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ and $0<d_{1K}<d_{2K}$, and a finite set $T_K$ of adelic matrices such that the union $\bigcup_{x\in T_K}(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\;K\,c_K\,u_K\,d_{1K}\,d_{2K}\,]$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre in the sense of `CoversModCentre`: every $g$ admits $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ in that union. Here the cut Siegel set consists of those $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal O}_K)$ and which satisfy, at every infinite place $w$, $\mathrm{localHeight}\ge c_K$, $\mathrm{xWindowSq}\le u_K^2$ and $\mathrm{archDetNorm}_w(g)\in[d_{1K},d_{2K}]$. Fix further a Haar measure $\nu_{Z_K}$ on the idele group, a set $\Omega_K$ which is a fundamental domain for the action of the image of $K^\times$ in the ideles, a finite set $S_K$ of finite places, a character $\xi_K$ of the full idele group (formally, of $(\top : \mathrm{Subgroup})$) with values in $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary, $\|\xi_K(z)\|=1$ for all $z$ (`hξu`), an ideal $N$ of $\mathcal O_K$ all of whose prime divisors lie in $S_K$ (`hN`), and an archimedean type family $\mathrm{tys}_K$ (a number of types at each infinite place, each given by a representation of the row-isometry group of the completion).
--
--   Let $\alpha_m$ be the real-valued idelic module character obtained from $\mathrm{distribHaarChar}(\mathbb{A}_K)$ by composing with $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passing to units; the adele ring carries its Borel structure. Assume $\alpha_m$ is everywhere positive (`hαm`).
--
--   Spectral data. Let $\iota_E$ be a countable type and $\mu,\nu:\iota_E\to \mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ families of characters subject to: unitarity ($\|\mu_e(z)\|=\|\nu_e(z)\|=1$), triviality on the image of $K^\times$ (`IsIdeleClassChar`), continuity, the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $e$ and $z$, and the separation hypothesis `_hdist`: distinct indices $e\ne e'$ are separated by some norm-one idele $z$ (an element of the kernel of $\mathrm{distribHaarChar}$) at which $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$.
--
--   Sections. Let $n_E:\iota_E\to\mathbb{N}$ and $\varphi_{e,j}:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ for $j\in\mathrm{Fin}(n_E\,e)$, written $\varphi_{e,j,s}$. The hypotheses on this family are: each $\varphi_{e,j,s}$ is an induced section for the pair of characters $\eta_1=\mu_e\,\alpha_m^{\,s+1/2}$, $\eta_2=\nu_e\,\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup (`_hφE`); archimedean $K$-finiteness at every infinite place (`_hφEK`); $K_f$-smoothness, i.e. an open stabiliser inside the finite adelic subgroup $\ker(\mathrm{glArch})$ (`_hφEf`); joint continuity in $(s,g)$ (`_hφEjc`); holomorphy in $s$ for each fixed $g$ (`_hφEhol`); a uniform $K$-finiteness hypothesis `_hφEKu`, asserting for each $e,j$ and each infinite place $w$ a finite-dimensional subspace $W$ of functions on $\mathrm{archRowIsometrySubgroup}\,K\,w$ containing all the right translates $k\mapsto\varphi_{e,j,s}(gk)$; flatness on the maximal compact, $\varphi_{e,j,s}(k)=\varphi_{e,j,0}(k)$ for $k\in\mathrm{adelicMaximalCompact}\,K$ (`_hφEflat`); right invariance under $\mathrm{principalLevel}\,N\sqcap\ker(\mathrm{glArch})$ (`_hφElev`); membership in the archimedean type submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$ (`_hφEty`); orthonormality on the maximal compact, $\int \varphi_{e,i,0}(k)\overline{\varphi_{e,j,0}(k)}\,d(\mathrm{maximalCompactHaar}\,K)=\delta_{ij}$ (`_hφEon`); a spanning hypothesis `_hφEspan`: for every $e$, every $t\in\mathbb{R}$ and every $\varphi_0$ that is an induced section for the characters at $s=it$, continuous, archimedean $K$-finite, right invariant under the level and of the prescribed archimedean types, $\varphi_0$ lies in the complex span of the $\varphi_{e,j,it}$; and a completeness-of-pairs hypothesis `_hpairs`: for every pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'=\xi_K$, every $t\in\mathbb{R}$ and every nonzero $\varphi_0$ with the same five properties at $s=it$, there is an index $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   Continuations. Let $O_{e,j}\subseteq\mathbb{C}$ and $E_{e,j},N_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, subject to the ten-clause hypothesis `_hEE`: $O_{e,j}$ is open and preconnected and contains both the line $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j,s}(g)$ and $s\mapsto N_{e,j,s}(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$ as functions of $(s,g)$; for $\mathrm{Re}\,s>1/2$ one has the Bruhat expansion $E_{e,j,s}(g)=\varphi_{e,j,s}(g)+\sum_{\xi\in K}\varphi_{e,j,s}(w\,n(\xi)\,g)$ with $w=\mathrm{adelicWeyl}$ and $n(\xi)$ the unipotent matrix with upper entry $\xi$; and for $\mathrm{Re}\,s>1/2$, $N_{e,j,s}(g)=\int_{\mathbb{A}_K}\varphi_{e,j,s}(w^{-1}n(x)g)\,dx$ is the Weyl intertwining integral against $\mathrm{adelicAddHaar}$.
--
--   Test function. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support, factorizable (`IsFactorizableTestFn`: $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and smooth in the mixed-space entries, $f_{\mathrm{fin}}$ locally constant with compact support), bi-invariant under $\mathrm{principalLevel}\,N\sqcap\ker(\mathrm{glArch})$, and archimedean bi-finite for $\mathrm{tys}_K$ (i.e. $g\mapsto f(g^{-1})$ lies in $\mathrm{archCutSubmodule}$ and $f$ in $\mathrm{archDualCutSubmodule}$).
--
--   Write, for $e\in\iota_E$, $i,j\in\mathrm{Fin}(n_E\,e)$ and $t\in\mathbb{R}$,
--   $$a^{(e)}_{ij}(t)=\int_{\mathbf K}\big(\mathrm{rightConv}\,\varphi_{e,j,it}\,f\big)(k)\,\overline{\varphi_{e,i,it}(k)}\;d(\mathrm{maximalCompactHaar}\,K),$$
--   where $(\mathrm{rightConv}\,\varphi\,f)(g)=\int \varphi(gx)f(x)\,dx$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, and put
--   $$\mathcal K(x,y)=\sum_{e}\int_{\mathbb{R}}\sum_{i}\sum_{j} a^{(e)}_{ij}(t)\,E_{e,i,it}(x)\,\overline{E_{e,j,it}(y)}\,dt .$$
--
--   The conclusion is the conjunction of six assertions.
--
--   First, for all $x,y\in\mathrm{GL}_2(\mathbb{A}_K)$: for every $e$ the function $t\mapsto\sum_{i,j}a^{(e)}_{ij}(t)\,E_{e,i,it}(x)\overline{E_{e,j,it}(y)}$ is integrable on $\mathbb{R}$, and the family of its $L^1$-norms, $e\mapsto\int_{\mathbb{R}}\big\|\sum_{i,j}a^{(e)}_{ij}(t)E_{e,i,it}(x)\overline{E_{e,j,it}(y)}\big\|\,dt$, is summable over $\iota_E$.
--
--   Second, the function $(x,y)\mapsto\mathcal K(x,y)$, given by the indicated $\mathrm{tsum}$ over $e$ of the $t$-integrals, is continuous on $\mathrm{GL}_2(\mathbb{A}_K)\times\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   Third, for every $\gamma\in \mathrm{GL}_2(K)$ and all $x,y$, $\mathcal K(\mathrm{globalPoints}(\gamma)\,x,\;y)=\mathcal K(x,y)$.
--
--   Fourth, for every $\gamma\in \mathrm{GL}_2(K)$ and all $x,y$, $\mathcal K(x,\;\mathrm{globalPoints}(\gamma)\,y)=\mathcal K(x,y)$.
--
--   Fifth, for every idele $a$ and all $x,y$, $\mathcal K(\mathrm{centralScalar}(a)\,x,\;y)=\xi_K(a)\,\mathcal K(x,y)$.
--
--   Sixth, for every idele $a$ and all $x,y$, $\mathcal K(x,\;\mathrm{centralScalar}(a)\,y)=\xi_K(a)^{-1}\,\mathcal K(x,y)$.
--
--   This is the regularity and equivariance statement for the Eisenstein (continuous-spectrum) part of the pointwise spectral kernel of a test function on $\mathrm{GL}_2$ over a number field: absolute convergence of the integral over the unitary axis together with summability over the countable family of character pairs, joint continuity of the resulting kernel, left invariance in each variable under $\mathrm{GL}_2(K)$, and transformation by the central character $\xi_K$ and its inverse in the two variables. It is used in the derivation of the pointwise spectral expansion, both in its almost-everywhere form on truncated domains and in its integrated form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_summable_and_continuous_uncurry_tsum_integral_sum_rightConv_axis_continuation_mul_conj.lean

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

theorem AutomorphicForm.integrable_and_summable_and_continuous_uncurry_tsum_integral_sum_rightConv_axis_continuation_mul_conj
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
    (∀ (x y : AdelicGL2 (𝓞 K) K),
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)))) ∧
      (Summable fun e : ιE => ∫ t : ℝ, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y))‖)) ∧
    (Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) p.1 * conj (EE e j ((t : ℂ) * Complex.I) p.2))) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) (AutomorphicForm.globalPoints (𝓞 K) K γ * x) * conj (EE e j ((t : ℂ) * Complex.I) y))) =
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)))) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.globalPoints (𝓞 K) K γ * y)))) =
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)))) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) (AutomorphicForm.centralScalar (𝓞 K) K a * x) * conj (EE e j ((t : ℂ) * Complex.I) y))) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) *
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)))) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.centralScalar (𝓞 K) K a * y)))) =
      (((ξK ⟨a, Subgroup.mem_top a⟩)⁻¹ : ℂˣ) : ℂ) *
      (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)))) := by sorry
