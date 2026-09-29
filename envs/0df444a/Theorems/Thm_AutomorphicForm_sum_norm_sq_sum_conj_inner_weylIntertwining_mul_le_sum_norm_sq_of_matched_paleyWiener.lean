-- Prove2me | Theorems.Thm_AutomorphicForm_sum_norm_sq_sum_conj_inner_weylIntertwining_mul_le_sum_norm_sq_of_matched_paleyWiener
-- name    : AutomorphicForm.sum_norm_sq_sum_conj_inner_weylIntertwining_mul_le_sum_norm_sq_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/15036dca-a2a3-5012-bcb0-1bf11e5f07a6
-- title:
--   Bessel bound for K-pairings of intertwined and flat families
-- statement:
--   Throughout, $K$ is a number field, $G = \mathrm{GL}_2$ of the adele ring of $K$ (written `AdelicGL2 (𝓞 K) K`), and $\mathbf{K}$ denotes the compact subgroup `adelicMaximalCompact K`, consisting of those $g$ whose finite part is integral and whose component at each infinite place $w$ is a row isometry, equipped with its Haar measure `maximalCompactHaar K`.
--
--   **Truncation, covering and idelic data.** Real numbers $\alpha < \beta$ with $0 < \alpha$ fix the domain $D =$ `canonicalTruncationDomain K α β`. A set $\Phi_K$ of adelic matrices occurs as a parameter with no condition imposed on it. Real parameters $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$, $0 < d_{1K} < d_{2K}$ and a finite set $T_K \subseteq G$ are given such that the union $\bigcup_{x \in T_K} (\cdot\, x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` covers $G$ modulo the centre, in the sense of `CoversModCentre`: every $g \in G$ can be written, after multiplication on the left by a global point $\gamma \in \mathrm{GL}_2(K)$ and on the right by a central idelic scalar, as an element of that union; here the centre-cut Siegel set consists of the $g$ with integral finite part, with $c_K \le$ `localHeight` of each archimedean component, with `xWindowSq` of each archimedean component at most $u_K^2$, and with each archimedean determinant norm in $[d_{1K}, d_{2K}]$. A Haar measure $\nu_{ZK}$ on the idele units is given together with a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in the ideles. Further data: a finite set $S_K$ of finite places of $K$; a character $\xi_K$ of the full idele unit group (presented as a homomorphism from $\top$ to $\mathbb{C}^\times$), assumed continuous (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N$ of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and an archimedean type family `tysK`, whose associated submodule `archCutSubmodule K tysK` is the intersection over the infinite places $w$ of the sums of the type submodules of the finitely many representations prescribed at $w$.
--
--   The homomorphism $\alpha_m$ from the idele units to $\mathbb{R}^\times$ is the one induced by the module `distribHaarChar` of the adele ring, followed by the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passage to units; the hypothesis `hαm` states that $\alpha_m(x) > 0$ for all $x$. The carrier data used below is `pins` $=$ `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: Borel structure and Haar measure on $G$, domain $D$, centre subgroup $\top$, level subgroups $U(M) =$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators `heckeGen (𝓞 K) K v`, and for the cuspidality condition the adelic additive Haar measure conditioned on the box `adelicBox K`.
--
--   **Cuspidal basis data.** An index type $\iota$, functions $b_i : G \to \mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb{C}$ are given, subject to: `hb`, that each $\mathrm{cls}(i)$ is a cusp class for `pins`, $\xi_K$, $N$, $S_K$ (level $N$, vanishing Hecke and central data at the places of $S_K$, non-zero isotypic cuspidal submodule) and that $b_i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}(i)$ intersected with `archCutSubmodule K tysK`; `hbn` and `hbo`, that the $b_i$ are orthonormal for the pairing $\int_D b_i \overline{b_j}$ taken with respect to `adelicGLHaar (Fin 2) (𝓞 K) K`; `hbs`, that for each cusp class $\pi$ the fibre $\{i : \mathrm{cls}(i) = \pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the isotypic cuspidal submodule of $\pi$ intersected with `archCutSubmodule K tysK`; and `hbc`, completeness: every function $\varphi$ which is a smooth cuspidal automorphic function for `pins` and $\xi_K$, continuous, invariant under right translation by the level subgroup `pins.U N`, lying in `archCutSubmodule K tysK`, and orthogonal over $D$ to all $b_i$, vanishes almost everywhere on $D$.
--
--   **Continuous-spectrum datum.** A countable type $\iota_E$ indexes pairs of characters $\mu_e, \nu_e$ of the idele units, each unitary, trivial on $K^\times$ (`IsIdeleClassChar`), continuous, with $\mu_e \nu_e = \xi_K$, and pairwise distinguished on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16). For each $e$ a number $n_E(e)$ and functions $\varphi_{e,j}(s) : G \to \mathbb{C}$, $j < n_E(e)$, are given; the hypotheses on them (summarised here) require that each $\varphi_{e,j}(s)$ be an induced section for the characters `etaFst (μ e) αm hαm s` $= \mu_e \cdot \alpha_m^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $= \nu_e \cdot \alpha_m^{-(s+1/2)}$ along the adelic Borel subgroup, archimedean $\mathbf{K}$-finite, smooth for the finite part, jointly continuous in $(s,g)$, entire in $s$ for fixed $g$, with archimedean $\mathbf{K}$-translates lying in a fixed finite-dimensional space at each infinite place, flat (the restriction to $\mathbf{K}$ is independent of $s$), invariant under right translation by `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, contained in `archCutSubmodule K tysK`, orthonormal on $\mathbf{K}$ at $s = 0$ against `maximalCompactHaar K` (`_hφEon`), and spanning (`_hφEspan`): for each real $t$, every induced section at $s = it$ with the corresponding regularity, level and type properties lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it)$. The hypothesis `_hpairs` asserts exhaustion: every pair $(\mu', \nu')$ of continuous unitary idele class characters with $\mu'\nu' = \xi_K$ admitting a non-zero induced section at some $s = it$ with those properties agrees on the norm-one ideles with some $(\mu_e, \nu_e)$. Finally, sets $O_E(e,j) \subseteq \mathbb{C}$ and functions $E_{e,j}, N_{e,j}$ are given with `_hEE`: each $O_E(e,j)$ is open, preconnected, contains the imaginary axis and the half-plane $\mathrm{Re}\,s > 1/2$; $E_{e,j}(\cdot)(g)$ and $N_{e,j}(\cdot)(g)$ are analytic on a neighbourhood of $O_E(e,j)$ for each $g$, and jointly continuous on $O_E(e,j) \times G$; for $\mathrm{Re}\,s > 1/2$ one has $E_{e,j}(s)(g) = \varphi_{e,j}(s)(g) + \sum_{\xi \in K} \varphi_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr)$, with $w =$ `adelicWeyl (𝓞 K) K` and $u(\xi)$ the unipotent matrix attached to $\xi$, and $N_{e,j}(s)(g) = \int \varphi_{e,j}(s)(w^{-1} u(x) g)\,dx$ against the adelic additive Haar measure, that is the Weyl intertwining integral.
--
--   **Paley–Wiener packet datum.** A finite type $\iota_P$ indexes pairs $\mu_{P,e}, \nu_{P,e}$ of unitary, continuous idele class characters with $\mu_{P,e}(z)\nu_{P,e}(z) = \xi_K(z)$ for $z$ in the centre subgroup of `pins` (which is $\top$), together with a map $r : \iota_P \to \iota_P$ exchanging the two characters, $\mu_{P,r(e)} = \nu_{P,e}$ and $\nu_{P,r(e)} = \mu_{P,e}$, and a separation condition on the norm-one ideles for distinct indices. Sections $\psi_e(s) : G \to \mathbb{C}$ are given, with hypotheses (summarised here) that they are induced sections for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`, jointly continuous, holomorphic in $s$, archimedean $\mathbf{K}$-finite, smooth for the finite part, with uniformly finite-dimensional archimedean $\mathbf{K}$-translates, invariant under the level subgroup at $N$, of type `archCutSubmodule K tysK`, and subject to the vertical-strip domination `_hψdec`: for each $e$, each $n$, each $\sigma_0$ and each compact $C \subseteq G$ there is an integrable, bounded majorant $m$ with $(1+|t|)^n\,\|\psi_e(\sigma' + it)(g)\| \le m(t)$ for all $|\sigma'| \le \sigma_0$, all $t$ and all $g \in C$. A function $\psi$ on $G$ is given which is a slab profile for $\top$ and $\xi_K$ (measurable, invariant under left multiplication by unipotents and by global Borel points, transforming by $\xi_K$ under the centre, bounded on determinant-norm slabs, supported in a band of adelic heights) and which is represented, for every real $\sigma'$ and every $g$, by $\psi(g) = \sum_e (4\pi)^{-1}\int_{\mathbb{R}} \psi_e(\sigma' + it)(g)\,dt$. Matching data $e(\cdot) : \iota_P \to \iota_E$ and $\tau : \iota_P \to \mathbb{R}$ satisfy $\mu_{P,i} = \mu_{e(i)} \cdot \|\cdot\|^{i\tau_i}$ and $\nu_{P,i} = \nu_{e(i)} \cdot \|\cdot\|^{-i\tau_i}$, in terms of [`NumberField.TateGlobal.normPowChar K (τ i)`](def/NumberField_NormPowChar.html#L22).
--
--   **Conclusion.** For every $i \in \iota_P$, every real $t$ and every vector $x \in \mathbb{C}^{n_E(e(r(i)))}$,
--   $$\sum_{j < n_E(e(i))} \Bigl|\; \sum_{j' < n_E(e(r(i)))} \overline{B_{j j'}}\; x_{j'} \Bigr|^2 \;\le\; \sum_{j' < n_E(e(r(i)))} |x_{j'}|^2,$$
--   where
--   $$B_{j j'} = \int_{\mathbf{K}} v^{-1}\, N_{e(i),j}\bigl(i(t + \tau_i)\bigr)(k)\; \overline{\varphi_{e(r(i)),j'}\bigl(i(-t + \tau_{r(i)})\bigr)(k)}\; d k,$$
--   the measure being `maximalCompactHaar K` and $v$ the complex number obtained from the real volume of the box `adelicBox K` for the adelic additive Haar measure; the complex arguments of $N$ and $\varphi$ are the purely imaginary numbers $((t + \tau_i) : \mathbb{R}) \cdot i$ and $((-t + \tau_{r(i)}) : \mathbb{R}) \cdot i$ respectively.
--
--   This is Bessel's inequality in $L^2(\mathbf{K})$ for the matrix of $\mathbf{K}$-pairings between the volume-normalised Weyl-intertwining continuation $N_{e(i),\bullet}$ on the unitary axis and the flat orthonormal family $\varphi_{e(r(i)),\bullet}$ attached to the partner index, both systems being orthonormal on the maximal compact subgroup. It is used by [`AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric`](thm.html#AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric) to control the continuous-spectrum contribution of a matched level-$N$ Paley–Wiener datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_norm_sq_sum_conj_inner_weylIntertwining_mul_le_sum_norm_sq_of_matched_paleyWiener.lean

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

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open MeasureTheory
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.sum_norm_sq_sum_conj_inner_weylIntertwining_mul_le_sum_norm_sq_of_matched_paleyWiener
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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    ∀ (i : ιP) (t : ℝ) (x : Fin (nE (em (rP i))) → ℂ),
      ∑ j : Fin (nE (em i)), ‖∑ j' : Fin (nE (em (rP i))),
        conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) * x j'‖ ^ 2 ≤
      ∑ j' : Fin (nE (em (rP i))), ‖x j'‖ ^ 2 := by sorry
