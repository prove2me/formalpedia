-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3b12bff4-ca97-5937-91c2-2d35ab62465b
-- title:
--   Wave-packet form of a matched Paley–Wiener pseudo-Eisenstein series
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}$ its adele ring, and $G = \mathrm{GL}_2(\mathbb{A})$ is `AdelicGL2 (𝓞 K) K`, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`; the adele ring carries `adeleBorel` and `adelicAddHaar`.
--
--   **Fixed data.** Reals $\alpha,\beta$ with $0 < \alpha$ and $\alpha < \beta$, determining the canonical truncation domain $\Phi_0 =$ `canonicalTruncationDomain K α β` (the third component of the canonical truncation datum for $\alpha,\beta$); a set $\Phi_K \subseteq G$, which occurs in no further hypothesis and not in the conclusion; reals $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$, $0 < d_{1K} < d_{2K}$ and a finite set $T_K \subseteq G$ such that `hcovK` holds: the union of the right translates $\{g x : g \in \mathcal{S}\}$, $x \in T_K$, of the centre-cut Siegel set $\mathcal{S} =$ `centreCutSiegelSet K cK uK d₁K d₂K` (the $g$ whose finite part is integral, with $c_K \le$ `localHeight` of the archimedean component at every infinite place, with `xWindowSq` at most $u_K^2$ there, and with archimedean determinant norm in $[d_{1K}, d_{2K}]$ at every infinite place) covers $G$ modulo the centre: every $g \in G$ admits $\gamma \in \mathrm{GL}_2(K)$ and $z \in \mathbb{A}^\times$ with $\gamma g \cdot z$ in that union. Further, a Haar measure $\nu_{ZK}$ on $\mathbb{A}^\times$ (with the routine measurability and Borel instances for $\mathbb{A}^\times$) and a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_{ZK}$; a finite set $S_K$ of finite places; a character $\xi_K$ of the full idele unit group (presented as a homomorphism from the top subgroup to $\mathbb{C}^\times$) which is continuous (`hξc`), trivial on the principal ideles (`hξt`) and unitary, $\lVert \xi_K(z)\rVert = 1$ (`hξu`); an ideal $N \subseteq \mathcal{O}_K$ such that every place dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place $w$ a number `card w` of representations of the row-isometry subgroup of $K_w$, cutting out the submodule `archCutSubmodule K tysK` $= \bigsqcap_w \bigvee_i$ (type submodule of the $i$-th representation at $w$).
--
--   Write $\alpha_m$ for the monoid homomorphism $\mathbb{A}^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}$ by composing with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and assume `hαm`, that $\alpha_m$ takes positive values. Throughout, `pins` denotes `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier data with Borel structure and Haar measure on $G$, domain $\Phi_0$, centre $\top$, level subgroups $\Gamma(M) \cap G_f$, Hecke generators `heckeGen`, and the conditional additive Haar measure of $\mathbb{A}$ on `adelicBox K`.
--
--   **Assertion.** There exists $\kappa \in \mathbb{R}$ with $0 < \kappa$ — chosen before, hence independent of, all the data listed next — such that for every choice of the following data and hypotheses the conclusion below holds.
--
--   *Cusp-basis block.* A type $\iota$, functions $b_i : G \to \mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i) \in$ `HeckeEigensystem K ℂ` such that (`hb`) each $\mathrm{cls}(i)$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing eigenvalues $a_v, b_v$ at the places of $S_K$, and nonzero isotypic cusp submodule) and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with `archCutSubmodule K tysK`; (`hbn`) $\int_{\Phi_0} b_i \overline{b_i} = 1$ and (`hbo`) $\int_{\Phi_0} b_i \overline{b_j} = 0$ for $i \ne j$, both against the Haar measure of $G$; (`hbs`) for each cusp class $\pi$ the fibre $\{i : \mathrm{cls}(i) = \pi\}$ is finite and the complex span of the corresponding $b_i$ is the isotypic cusp submodule of $\pi$ met with `archCutSubmodule K tysK`; and (`hbc`) completeness: every $\varphi$ which is a smooth cuspidal automorphic function at `pins` for $\xi_K$, is continuous, is right invariant under `pins.U N`, lies in `archCutSubmodule K tysK` and satisfies $\int_{\Phi_0} \varphi \overline{b_i} = 0$ for all $i$, vanishes almost everywhere for the Haar measure restricted to $\Phi_0$.
--
--   *Eisenstein-family block.* A countable type $\iota_E$ and families $\mu, \nu : \iota_E \to \mathrm{Hom}(\mathbb{A}^\times, \mathbb{C}^\times)$ whose members are unitary, are idele class characters (trivial on $K^\times$), are continuous, satisfy $\mu_e \nu_e = \xi_K$ pointwise, and are separated in the sense that distinct $e \ne e'$ are distinguished by some norm-one idele (an element of the kernel of the distributive Haar character) through $\mu$ or through $\nu$. Integers $n_E(e)$ and sections $\varphi_{e,j}(s) : G \to \mathbb{C}$ for $j < n_E(e)$ subject to: each $\varphi_{e,j}(s)$ is an induced section for the pair $\bigl(\mu_e \alpha_m^{\,s+1/2},\ \nu_e \alpha_m^{-(s+1/2)}\bigr)$, i.e. $\varphi(bg) = \eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup; archimedean $K$-finiteness; $K_f$-smoothness; joint continuity in $(s,g)$; holomorphy in $s$ for each $g$; at each infinite place $w$ a finite-dimensional space of functions on the row-isometry subgroup containing all the right-translate functions $k \mapsto \varphi_{e,j}(s)(gk)$; flatness, $\varphi_{e,j}(s)(k) = \varphi_{e,j}(0)(k)$ on the adelic maximal compact subgroup; right invariance under $\Gamma(N) \cap G_f$; membership in `archCutSubmodule K tysK`; orthonormality at $s=0$ over the maximal compact subgroup with its Haar measure, $\int \varphi_{e,i}(0)\overline{\varphi_{e,j}(0)} = \delta_{ij}$; completeness on the unitary axis (`_hφEspan`), namely every continuous, archimedean $K$-finite, level-$N$ invariant section of type $\mathrm{tys}_K$ induced from the pair at $s = it$ lies in the span of the $\varphi_{e,j}(it)$; and matching (`_hpairs`), namely every pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu' = \xi_K$ that carries a nonzero such section at some point $it$ agrees, on the norm-one ideles, with some $(\mu_e,\nu_e)$. Finally sets $O_{e,j} \subseteq \mathbb{C}$ and functions $E_{e,j}(s), N_{e,j}(s) : G \to \mathbb{C}$ with (`_hEE`) $O_{e,j}$ open, preconnected, containing the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; $s \mapsto E_{e,j}(s)(g)$ and $s \mapsto N_{e,j}(s)(g)$ analytic on a neighbourhood of each point of $O_{e,j}$ for every $g$; both jointly continuous on $O_{e,j} \times G$; and, for $\mathrm{Re}\,s > 1/2$, $E_{e,j}(s)(g) = \varphi_{e,j}(s)(g) + \sum_{\xi \in K}' \varphi_{e,j}(s)(w\, n(\xi)\, g)$ with $w$ the adelic Weyl element and $n(\cdot)$ the unipotent embedding, while $N_{e,j}(s)(g) = \int_{\mathbb{A}} \varphi_{e,j}(s)(w^{-1} n(x) g)\,dx$ for the additive Haar measure of $\mathbb{A}$.
--
--   *Paley–Wiener packet block.* A finite type $\iota_P$ and families $\mu_P, \nu_P : \iota_P \to \mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$, each member unitary, an idele class character and continuous, with $\mu_P(e)(z)\nu_P(e)(z) = \xi_K(z)$ for $z$ in the centre `pins.Z`; a map $r_P : \iota_P \to \iota_P$ with $\mu_P(r_P e) = \nu_P(e)$ and $\nu_P(r_P e) = \mu_P(e)$; separation of distinct indices by some norm-one idele. Sections $\psi_e(s) : G \to \mathbb{C}$ which are induced sections for $\bigl(\mu_P(e)\alpha_m^{\,s+1/2}, \nu_P(e)\alpha_m^{-(s+1/2)}\bigr)$, jointly continuous, holomorphic in $s$, archimedean $K$-finite, $K_f$-smooth, with finite-dimensional archimedean $K$-type spaces at each infinite place, and rapidly decreasing uniformly in vertical strips (`_hψdec`): for all $e$, $n \in \mathbb{N}$, $\sigma_0 \in \mathbb{R}$ and compact $C \subseteq G$ there is an integrable, bounded above $m : \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^n \lVert \psi_e(\sigma' + it)(g)\rVert \le m(t)$ for $|\sigma'| \le \sigma_0$, all $t$ and all $g \in C$. A function $\psi : G \to \mathbb{C}$ which is a slab profile for the centre $\top$ and $\xi_K$ (measurable; invariant under left multiplication by adelic unipotents; invariant under the global Borel subgroup; transforming by $\xi_K$ under the centre; bounded on each determinant-idele-norm slab $[d_1,d_2]$ with $d_1 > 0$; and nonvanishing only where the adelic height lies in some band $[a,b]$ with $a > 0$), and which is represented by its packet on every vertical line (`_hψrep`): $\psi(g) = \sum_{e \in \iota_P} (4\pi)^{-1}\int_{\mathbb{R}} \psi_e(\sigma' + it)(g)\,dt$ for all $\sigma' \in \mathbb{R}$ and $g \in G$. Maps $\mathrm{em} : \iota_P \to \iota_E$ and $\tau : \iota_P \to \mathbb{R}$ with (`_hem`) $\mu_P(i) = \mu_{\mathrm{em}(i)} \cdot \lVert\cdot\rVert^{\,i\tau_i}$ and $\nu_P(i) = \nu_{\mathrm{em}(i)} \cdot \lVert\cdot\rVert^{-i\tau_i}$ in terms of `normPowChar`; and right invariance of each $\psi_i(s)$ under $\Gamma(N) \cap G_f$ together with membership in `archCutSubmodule K tysK`.
--
--   *Residual projection block.* A function $p_\psi : G \to \mathbb{C}$ satisfying the predicate `IsAutomorphicFnAt` at `pins` for $\xi_K$ (the predicate `LsXiMember` for the Haar measure of $G$, the centre $\top$, the character $\xi_K$ and the domain $\Phi_0$), which is approximable by residual functions (`_hpψc`): for every $\varepsilon > 0$ there is $r$ in the residual span — the complex span of the functions $g \mapsto \chi(\det g)$ for characters $\chi$ with $\chi^2 = \xi_K$ on the centre — satisfying the same automorphy predicate and $\lVert p_\psi - r\rVert_{L^2}$, taken for the Haar measure restricted to $\Phi_0$, less than $\varepsilon$; and which is the orthogonal projection datum (`_hpψo`): for every $h$ satisfying the automorphy predicate and lying in the residual span, $\int_{\Phi_0} \bigl(\mathrm{Eis}(\psi)(g) - p_\psi(g)\bigr)\overline{h(g)}\,dg = 0$, where $\mathrm{Eis}(\psi)(g) = \psi(g) + \sum_{\beta \in K}' \psi(w\,n(\beta)\,g)$ is the pseudo-Eisenstein series of $\psi$.
--
--   **Conclusion.** With the Haar measure of $G$ restricted to $\Phi_0$, the function $g \mapsto \mathrm{Eis}(\psi)(g) - p_\psi(g)$ agrees almost everywhere with
--   $$g \;\longmapsto\; \kappa \sum_{i \in \iota_P} \int_{\mathbb{R}} \sum_{j < n_E(\mathrm{em}(i))} \left( \int_{\mathcal{K}} \psi_i(it)(k)\, \overline{\varphi_{\mathrm{em}(i),j}\bigl(i(t+\tau_i)\bigr)(k)} \, dk \right) E_{\mathrm{em}(i),j}\bigl(i(t+\tau_i)\bigr)(g) \, dt,$$
--   where $\mathcal{K}$ is the adelic maximal compact subgroup with its Haar measure `maximalCompactHaar K`, and the constant $\kappa$ is real, viewed in $\mathbb{C}$.
--
--   This is Langlands' wave-packet (contour-shift) representation of a pseudo-Eisenstein series attached to a Paley–Wiener datum, written on the unitary axis and expanded in the complete orthonormal families of flat sections, in its one-term form: each index $i$ of the packet contributes only through its own sections paired against the family of the matched pair $\mathrm{em}(i)$ at the shifted point $i(t+\tau_i)$, the residual part having been subtracted off by the projection $p_\psi$. It supplies the continuous-spectrum input for the subsequent statements that bound and compute, in terms of axis pairings, the continuous contribution to the spectral decomposition on the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener.lean

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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
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
    ∃ κ : ℝ, 0 < κ ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
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
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    (fun g : AdelicGL2 (𝓞 K) K => AutomorphicForm.pseudoEisenstein K ψ g - pψ g)
      =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
    fun g : AdelicGL2 (𝓞 K) K =>
      (κ : ℂ) * ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g := by sorry
