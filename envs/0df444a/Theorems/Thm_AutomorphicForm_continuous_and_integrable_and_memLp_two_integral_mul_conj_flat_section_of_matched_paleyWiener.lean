-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
-- name    : AutomorphicForm.continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/2e0f9aea-05e9-5348-9014-2e1f9249e341
-- title:
--   Continuity, integrability and L²-ness of wave-packet coefficients
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal O_K$, $\mathbb A$ denotes its adele ring, and $G = \mathrm{GL}_2(\mathbb A)$ (the Lean `AdelicGL2 (𝓞 K) K`), equipped with its Borel $\sigma$-algebra and Haar measure. Two real parameters $0 < \alpha < \beta$ are fixed, and $D =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the domain component of a chosen truncation datum for $(\alpha,\beta)$.
--
--   **Siegel covering data.** A set $\Phi_K \subseteq G$, reals $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$ and $0 < d_{1K} < d_{2K}$, and a finite set $T_K \subseteq G$ are given, together with the hypothesis `hcovK` that the set $\bigcup_{x \in T_K} (\,\cdot\, x)\bigl[\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}\bigr]$ covers $G$ modulo the centre: for every $g \in G$ there are $\gamma \in \mathrm{GL}_2(K)$ and $z \in \mathbb A^\times$ such that $\gamma g\,z$ (global point times $g$ times central scalar) lies in that union. The centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean component at every infinite place $w$ has local height $\ge c_K$ and window coordinate $\mathrm{xWindowSq} \le u_K^2$, and whose archimedean determinant norm at every $w$ lies in $[d_{1K}, d_{2K}]$.
--
--   **Central measure data.** A measurable structure on $\mathbb A^\times$ which is the Borel structure of its topology, a Haar measure $\nu_{Z,K}$ on $\mathbb A^\times$, and a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in $\mathbb A^\times$ with respect to $\nu_{Z,K}$.
--
--   **Character, level and type data.** A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top$ of $\mathbb A^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on the principal ideles coming from $K^\times$ (`hξt`) and of absolute value $1$ at every idele (`hξu`); an ideal $N \subseteq \mathcal O_K$ all of whose prime divisors lie in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place $w$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$, cutting out the submodule `archCutSubmodule K tysK`.
--
--   The statement then introduces $\alpha_m$, the character of $\mathbb A^\times$ with values in $\mathbb R^\times$ obtained from the distributive Haar character of $\mathbb A$ by passing through $\mathbb R_{\ge 0} \to \mathbb R$ and to units, and quantifies over the hypothesis `hαm` that $\alpha_m(x) > 0$ for all $x$. All the following data are universally quantified, with $\mathrm{pins} =$ `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, so that the carrier is $D$, the centre is $\top$, the level subgroup at $M$ is $\Gamma(M) =$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators are the `heckeGen` elements, and the cuspidality measure is Haar on $\mathbb A$ conditioned on the adelic box.
--
--   **Cusp-basis data.** A type $\iota$, functions $b : \iota \to (G \to \mathbb C)$ and $\mathrm{cls} : \iota \to$ `HeckeEigensystem K ℂ`, subject to: `hb`, each $\mathrm{cls}(i)$ is a cusp class for $(\mathrm{pins}, \xi_K, N, S_K)$ (level $N$, vanishing $a_v, b_v$ at $v \in S_K$, nonzero isotypic submodule) and $b(i)$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with the archimedean cut submodule; `hbn`, $\int_D b(i)\overline{b(i)} = 1$ against Haar on $G$; `hbo`, $\int_D b(i)\overline{b(j)} = 0$ for $i \ne j$; `hbs`, for every cusp class $\pi$ the fibre $\{i \mid \mathrm{cls}(i) = \pi\}$ is finite and the $\mathbb C$-span of its $b$-image is the full isotypic-cut submodule of $\pi$; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $(\mathrm{pins},\xi_K)$, continuous, right $\Gamma(N)$-invariant, in the archimedean cut submodule, and orthogonal over $D$ to every $b(i)$, vanishes almost everywhere on $D$.
--
--   **Continuous-spectrum frame.** A countable type $\iota_E$ and characters $\mu_e, \nu_e : \mathbb A^\times \to \mathbb C^\times$ ($e \in \iota_E$) which are unitary, trivial on principal ideles, continuous, satisfy $\mu_e\nu_e = \xi_K$, and are pairwise separated on the norm-one ideles (`_hdist`). For each $e$ an integer $n_E(e)$ and sections $\varphi^E_{e,j}(s) : G \to \mathbb C$ for $j < n_E(e)$, $s \in \mathbb C$, subject to the hypothesis group `_hφE`–`_hφEspan`: each $\varphi^E_{e,j}(s)$ is an induced section for the pair $\bigl(\mu_e\,\alpha_m^{s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\bigr)$ (transforming by these characters on the diagonal entries under left translation by the adelic Borel), is archimedean $\mathbf K$-finite, is smooth for the finite adelic subgroup, is jointly continuous in $(s,g)$, holomorphic in $s$ for fixed $g$, has all right translates by the row-isometry subgroup at each infinite place inside one fixed finite-dimensional space, is flat (its restriction to the adelic maximal compact subgroup is independent of $s$, equal to that of $s = 0$), is right $\Gamma(N)$-invariant, lies in the archimedean cut submodule, is orthonormal on the maximal compact subgroup at $s = 0$ ($\int \varphi^E_{e,i}(0)\overline{\varphi^E_{e,j}(0)} \, d k = \delta_{ij}$ against `maximalCompactHaar K`), and spans, on each point $s = it$ of the imaginary axis, all induced sections for $(\mu_e,\nu_e)$ at that point which are continuous, archimedean $\mathbf K$-finite, $\Gamma(N)$-invariant and of the prescribed archimedean type. The hypothesis `_hpairs` states that every admissible pair $(\mu',\nu')$ (unitary, trivial on principal ideles, continuous, with product $\xi_K$) admitting a nonzero such section at some $s = it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   **Axis continuations.** Sets $O_{e,j} \subseteq \mathbb C$ and families $E_{e,j}(s), N_{e,j}(s) : G \to \mathbb C$, subject to `_hEE`: each $O_{e,j}$ is open, preconnected, and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s > 1/2$; for each $g$, $s \mapsto E_{e,j}(s)(g)$ and $s \mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j} \times G$ jointly; for $\mathrm{Re}\,s > 1/2$ one has the Eisenstein expansion $E_{e,j}(s)(g) = \varphi^E_{e,j}(s)(g) + \sum_{\xi \in K}' \varphi^E_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix, and $N_{e,j}(s)(g)$ is the Weyl intertwining integral $\int_{\mathbb A} \varphi^E_{e,j}(s)\bigl(w^{-1}u(x)g\bigr)\,dx$ against adelic additive Haar measure.
--
--   **Paley–Wiener packet data.** A finite type $\iota_P$ and characters $\mu_{P,e}, \nu_{P,e}$ which are unitary, trivial on principal ideles, continuous, satisfy $\mu_{P,e}\nu_{P,e} = \xi_K$ on the centre $\top$, are permuted by an involution-like map $r_P$ swapping $\mu_P$ and $\nu_P$, and are pairwise separated on the norm-one ideles. Sections $\psi^f_e(s) : G \to \mathbb C$ are given which are induced sections for $\bigl(\mu_{P,e}\alpha_m^{s+1/2}, \nu_{P,e}\alpha_m^{-(s+1/2)}\bigr)$, jointly continuous, holomorphic in $s$, archimedean $\mathbf K$-finite, smooth for the finite adelic subgroup, with uniformly finite-dimensional right translates under each archimedean row-isometry subgroup, right $\Gamma(N)$-invariant (`_hψlev`), of the prescribed archimedean type (`_hψty`), and satisfying the vertical-strip decay hypothesis `_hψdec`: for every $e$, every $n \in \mathbb N$, every $\sigma_0 \in \mathbb R$ and every compact $C \subseteq G$ there is an integrable and bounded $m : \mathbb R \to \mathbb R$ with $(1+|t|)^n\,\|\psi^f_e(\sigma'+it)(g)\| \le m(t)$ for all $|\sigma'| \le \sigma_0$, all $t$ and all $g \in C$. A function $\psi : G \to \mathbb C$ is given which is a slab profile for $(\top, \xi_K)$ — measurable, invariant under left translation by unipotents and by global Borel points, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab, and supported in a band of adelic heights — and which is represented, for every $\sigma' \in \mathbb R$ and every $g$, by $\psi(g) = \sum_{e \in \iota_P} (4\pi)^{-1}\int_{\mathbb R} \psi^f_e(\sigma'+it)(g)\,dt$. Finally a matching $\mathrm{em} : \iota_P \to \iota_E$ and shifts $\tau : \iota_P \to \mathbb R$ are given with $\mu_{P,i} = \mu_{\mathrm{em}(i)}\cdot \|\cdot\|^{i\tau_i}$ and $\nu_{P,i} = \nu_{\mathrm{em}(i)}\cdot \|\cdot\|^{-i\tau_i}$, where $\|\cdot\|^{it}$ is [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22).
--
--   **Conclusion.** For every $i \in \iota_P$ and every $j < n_E(\mathrm{em}(i))$, put
--   $$c(t) \;=\; \int_{\mathbf K} \psi^f_i(it)(k)\;\overline{\varphi^E_{\mathrm{em}(i),j}\bigl(i(t+\tau_i)\bigr)(k)}\; d k \qquad (t \in \mathbb R),$$
--   the integral being over the adelic maximal compact subgroup $\mathbf K =$ `adelicMaximalCompact K` against `maximalCompactHaar K`. Then $c$ is continuous on $\mathbb R$, $c$ is integrable with respect to Lebesgue measure, and $c$ belongs to $L^2$ of Lebesgue measure.
--
--   This is the analytic input on the coefficient functions that pair a Paley–Wiener section against a flat orthonormal section of a continuous family: the coefficient $t \mapsto c(t)$ of the axis continuation $E_{\mathrm{em}(i),j}(i(t+\tau_i))$ in the Eisenstein wave packet attached to the slab profile $\psi$. It is used by the statements that establish square-integrability over the truncation domain of the wave packet formed from the axis continuations and their Weyl intertwining terms, and the corresponding finiteness of the associated $L^2$ integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.continuous_and_integrable_and_memLp_two_integral_mul_conj_flat_section_of_matched_paleyWiener
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
    ∀ (i : ιP) (j : Fin (nE (em i))),
    let c : ℝ → ℂ := fun t =>
      (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K))
    Continuous c ∧ Integrable c ∧ MemLp c 2 := by sorry
