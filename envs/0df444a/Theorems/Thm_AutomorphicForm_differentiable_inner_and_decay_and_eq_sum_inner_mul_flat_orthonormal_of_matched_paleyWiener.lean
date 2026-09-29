-- Prove2me | Theorems.Thm_AutomorphicForm_differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
-- name    : AutomorphicForm.differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/fb53bff4-e6eb-5c0c-96a9-f260f4611a06
-- title:
--   Off-axis K-expansion of matched Paley–Wiener sections
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring, $\mathbf{G} = \mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`), and $\mathbf{K} =$ `adelicMaximalCompact K` the subgroup of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component at each infinite place $w$ is a row isometry; `maximalCompactHaar K` is the Haar measure on $\mathbf{K}$, and `adelicGLHaar (Fin 2) (𝓞 K) K` the Haar measure on $\mathbf{G}$ for the Borel structure `glBorel`.
--
--   **Geometric and central data.** Real numbers $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$ determine the truncation region $D =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32); a set $\Phi_K \subseteq \mathbf{G}$ is also among the data. Real numbers $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$ and $0 < d_{1K} < d_{2K}$ and a finite set $T_K \subseteq \mathbf{G}$ satisfy `hcovK`: the union $\bigcup_{x \in T_K} \Sigma x$ of right translates of the centre-cut Siegel set $\Sigma =$ `centreCutSiegelSet K cK uK d₁K d₂K` (those $g$ with integral finite part, with $c_K \le$ `localHeight` and `xWindowSq` $\le u_K^2$ at every infinite place, and archimedean determinant norm in $[d_{1K}, d_{2K}]$) covers $\mathbf{G}$ modulo the centre and $\mathrm{GL}_2(K)$, in the sense of `CoversModCentre`. A Haar measure $\nu_{Z,K}$ on $\mathbb{A}_K^\times$ is given together with a set $\Omega_K$ that is a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$.
--
--   **Central character, level, types.** $S_K$ is a finite set of finite places of $K$; $\xi_K$ is a homomorphism from the full group $\mathbb{A}_K^\times$ (presented as the top subgroup) to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and `tysK` is an `ArchTypeFamily` for $K$, cutting out the submodule `archCutSubmodule K tysK`. The homomorphism $\alpha_m : \mathbb{A}_K^\times \to \mathbb{R}^\times$ is obtained from the distributive Haar character of $\mathbb{A}_K$ composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and `hαm` asserts that all its values are positive. The `CarrierPins` structure used below is `productionPinsOf` for the region $D$, the level subgroups $M \mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v` and the box `adelicBox K`; its central subgroup is all of $\mathbb{A}_K^\times$.
--
--   **Cuspidal orthonormal family (`hb`, `hbn`, `hbo`, `hbs`, `hbc`).** A type $\iota$, functions $b : \iota \to (\mathbf{G} \to \mathbb{C})$ and $cls : \iota \to$ `HeckeEigensystem K ℂ` are given with: each $cls\,i$ in `cuspClasses` for these pins, $\xi_K$, $N$, $S_K$, and $b\,i$ in the intersection of the isotypic cusp submodule of $cls\,i$ with the archimedean type cut; the $b\,i$ orthonormal for the pairing $\int_D b\,i\cdot \overline{b\,j}$ against the Haar measure on $\mathbf{G}$; for each cusp class $\pi$ the fibre $\{i : cls\,i = \pi\}$ finite with $\mathbb{C}$-span of its $b$-image equal to the $\pi$-isotypic cusp submodule intersected with the type cut; and completeness (`hbc`): any $\varphi$ that is a smooth cuspidal automorphic function for the pins and $\xi_K$, continuous, right invariant under the level-$N$ subgroup, of the prescribed archimedean type, and orthogonal to every $b\,i$ over $D$, vanishes almost everywhere for the Haar measure restricted to $D$.
--
--   **Eisenstein pairs and flat orthonormal sections.** A countable type $\iota_E$ carries families $\mu, \nu : \iota_E \to \mathrm{Hom}(\mathbb{A}_K^\times, \mathbb{C}^\times)$ whose members are unitary, trivial on $K^\times$, continuous, satisfy $\mu_e \nu_e = \xi_K$, and are pairwise distinguished on the norm-one ideles. Integers $n_E(e)$ and functions $\varphi_{e,j,s} =$ `φE e j s` ($j \in \mathrm{Fin}\,(n_E\,e)$) satisfy a block of hypotheses (summarised here): each $\varphi_{e,j,s}$ is an induced section for the characters `etaFst (μ e) αm hαm s` $= \mu_e \cdot \alpha_m^{s + 1/2}$ and `etaSnd (ν e) αm hαm s` $= \nu_e \cdot \alpha_m^{-(s+1/2)}$ on the diagonal entries of the adelic Borel subgroup; archimedean $K$-finite; $K_f$-smooth; jointly continuous in $(s,g)$; entire in $s$ for each $g$; $K$-finite with a single finite-dimensional space of right translates at each infinite place, uniformly in $s$ and $g$; flat, in that its restriction to $\mathbf{K}$ is independent of $s$; invariant under right translation by the level-$N$ subgroup; of the prescribed archimedean type; orthonormal on $\mathbf{K}$ at $s = 0$ for `maximalCompactHaar K`; and spanning, in that on the unitary axis every continuous, archimedean $K$-finite, level-$N$-invariant induced section of the prescribed type for the parameter $it$ lies in the $\mathbb{C}$-span of the $\varphi_{e,j,it}$. A further hypothesis `_hpairs` asserts that the family $(\mu_e,\nu_e)_e$ exhausts the relevant pairs: for any continuous unitary idele class characters $\mu', \nu'$ with $\mu'\nu' = \xi_K$ admitting a nonzero section with the listed properties at parameter $it$, some $e$ agrees with $(\mu',\nu')$ on the norm-one ideles. The data $O_E(e,j) \subseteq \mathbb{C}$, $E_E(e,j,s)$, $N_E(e,j,s)$ satisfy `_hEE` (nine clauses): $O_E(e,j)$ is open, preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s > 1/2$; $E_E$ and $N_E$ are analytic in $s$ on a neighbourhood of $O_E(e,j)$ for each $g$ and jointly continuous on $O_E(e,j) \times \mathbf{G}$; and for $\mathrm{Re}\,s > 1/2$ one has $E_E(e,j,s)(g) = \varphi_{e,j,s}(g) + \sum_{\xi \in K}^{} \varphi_{e,j,s}(w\,u(\xi)\,g)$ with $w =$ `adelicWeyl` and $u$ the unipotent embedding, and $N_E(e,j,s)(g)$ equal to the Weyl intertwining integral of $\varphi_{e,j,s}$ at $g$ for the additive adelic Haar measure.
--
--   **Paley–Wiener packet.** A finite type $\iota_P$ carries characters $\mu_P, \nu_P$ that are unitary, trivial on $K^\times$, continuous, satisfy $\mu_P(e)\,\nu_P(e) = \xi_K$ on the central subgroup of the pins, are pairwise distinguished on the norm-one ideles, and are interchanged by a map $r_P : \iota_P \to \iota_P$. Sections $\psi_f(e,s)$ are induced sections for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`, jointly continuous in $(s,g)$, entire in $s$, archimedean $K$-finite, $K_f$-smooth, uniformly $K$-finite at each infinite place, invariant under the level-$N$ subgroup, of the prescribed archimedean type, and rapidly decreasing on vertical lines uniformly on strips and compacta (`_hψdec`): for all $e$, $n \in \mathbb{N}$, $\sigma_0 \in \mathbb{R}$ and compact $C \subseteq \mathbf{G}$ there is an integrable $m : \mathbb{R} \to \mathbb{R}$, bounded above, with $(1+|t|)^n \|\psi_f(e,\sigma'+it)(g)\| \le m(t)$ for $|\sigma'| \le \sigma_0$, all $t$, and all $g \in C$. A function $\psi : \mathbf{G} \to \mathbb{C}$ is a slab profile for the central subgroup and $\xi_K$ (measurable; left invariant under unipotents and under the $K$-rational Borel subgroup; transforming by $\xi_K$ under the centre; bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1 > 0$; and non-vanishing only where the adelic height lies in a fixed band $[a,b]$ with $a > 0$), and `_hψrep` asserts that for every $\sigma' \in \mathbb{R}$ and every $g$, $\psi(g) = \sum_{e \in \iota_P} (4\pi)^{-1} \int_{\mathbb{R}} \psi_f(e,\sigma'+it)(g)\,dt$. Finally, maps $em : \iota_P \to \iota_E$ and $\tau : \iota_P \to \mathbb{R}$ match the packet to the Eisenstein pairs: $\mu_P(i) = \mu_{em(i)} \cdot$ `normPowChar K (τ i)` and $\nu_P(i) = \nu_{em(i)} \cdot ($`normPowChar K (τ i)`$)^{-1}$, where `normPowChar K t` is $x \mapsto \|x\|^{it}$ in terms of the idele norm.
--
--   **Conclusion.** For a fixed $i \in \iota_P$, writing
--   $$c_{i,j}(s) = \int_{\mathbf{K}} \psi_f(i,s)(k)\,\overline{\varphi_{em(i),j,\,s + i\tau_i}(k)}\ dk$$
--   for the Haar measure `maximalCompactHaar K`, three assertions hold. First, for every $j \in \mathrm{Fin}\,(n_E(em\,i))$ the function $s \mapsto c_{i,j}(s)$ is complex differentiable on all of $\mathbb{C}$. Second, for every such $j$, every $n \in \mathbb{N}$ and every $\sigma_0 \in \mathbb{R}$ there exists $m : \mathbb{R} \to \mathbb{R}$ that is integrable and bounded above by some constant $B$, such that $(1+|t|)^n\,\|c_{i,j}(\sigma'+it)\| \le m(t)$ for all real $\sigma'$ with $|\sigma'| \le \sigma_0$ and all real $t$. Third, for every $s \in \mathbb{C}$ and every $g \in \mathbf{G}$,
--   $$\psi_f(i,s)(g) = \sum_{j \in \mathrm{Fin}(n_E(em\,i))} c_{i,j}(s)\ \varphi_{em(i),j,\,s+i\tau_i}(g),$$
--   a finite sum over the flat orthonormal family at the shifted parameter $s + i\tau_i$.
--
--   This is the off-axis expansion of a matched Paley–Wiener section in the flat orthonormal family of induced sections attached to its Eisenstein pair, together with holomorphy and uniform rapid decay of the resulting coefficient functions on vertical strips. It feeds the contour-shift analysis of pseudo-Eisenstein wave packets, being used in the finiteness estimate for the $L^2$-mass of the shifted packet built from these coefficients, the Eisenstein continuation and the Weyl intertwining operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (i : ιP),
    (∀ j : Fin (nE (em i)), Differentiable ℂ (fun s : ℂ =>
        ∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) ∧
    (∀ (j : Fin (nE (em i))) (n : ℕ) (σ₀ : ℝ), ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
        ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
          (1 + |t|) ^ n * ‖∫ k, ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((σ' : ℂ) + (t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤ m t) ∧
    ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      ψf i s g = ∑ j : Fin (nE (em i)),
        (∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) g := by sorry
