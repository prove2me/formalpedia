-- Prove2me | Theorems.Thm_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/30ad678d-6c21-566a-b708-cc4ba634c0b1
-- title:
--   Merging two matched Paley–Wiener families over one index set
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha<\beta$, and $\Phi K$ is a set of elements of $\mathrm{GL}_2$ of the adele ring of $K$ (written `AdelicGL2 (𝓞 K) K`).
--
--   **Covering data.** Reals $cK,uK,d_1K,d_2K$ with $0<cK$, $0<d_1K<d_2K$ and a finite set $TK\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ are given, subject to `hcovK`: the union $\bigcup_{x\in TK}\{h\,x\}$ of right translates of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` — the set of $g$ whose finite part lies in `finiteIntegralGL2`, with `localHeight` of the component at each infinite place $w$ at least $cK$, with `xWindowSq` of that component at most $uK^2$, and with `archDetNorm` at each $w$ in $[d_1K,d_2K]$ — covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\,g\,z\cdot 1$ in that union.
--
--   **Central measure data.** The idele unit group carries a measurable structure which is the Borel structure of its topology, $\nu ZK$ is a Haar measure on it, and $\Omega K$ is a fundamental domain (`hΩK`) for the subgroup of principal ideles, the range of $K^\times\to\mathbb{A}_K^\times$, acting with respect to $\nu ZK$.
--
--   **Central character and level.** $SK$ is a finite set of finite places, and $\xi K$ is a homomorphism from the full subgroup of ideles to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles (`hξt`) and unitary (`hξu`, $\lVert\xi K(z)\rVert=1$ for all $z$). $N$ is an ideal of $\mathcal{O}_K$ with every prime dividing $N$ in $SK$ (`hN`), and $tysK$ is an `ArchTypeFamily`, i.e. for each infinite place $w$ a finite list of representations of the row-isometry group at $w$, cutting out the submodule `archCutSubmodule K tysK`.
--
--   The character $\alpha m$ is the positive real character of the ideles obtained from the distributive Haar character (module) of multiplication on $\mathbb{A}_K$, and $h\alpha m$ asserts $\alpha m(x)>0$ for all $x$. Throughout, `pins` abbreviates `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier package whose measurable structure is the Borel one, whose measure is the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, whose domain is the canonical truncation domain of parameters $\alpha,\beta$, whose central subgroup is all of $\mathbb{A}_K^\times$, whose level subgroups are $\mathrm{principalLevel}(M)\sqcap$ the finite-adelic subgroup (the kernel of the archimedean projection), whose Hecke generators are `heckeGen`, and whose additive measure is the adelic additive Haar measure conditioned on the box `adelicBox K`.
--
--   **Cuspidal frame.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $cls:\iota\to$ `HeckeEigensystem K ℂ` are given with: `hb`, each $cls\,i$ is a cusp class for `pins`, $\xi K$, $N$, $SK$ (level $N$, vanishing Hecke and central data at the places of $SK$, non-zero isotypic cuspidal submodule) and $b\,i$ lies in the isotypic cuspidal submodule of $cls\,i$ intersected with `archCutSubmodule K tysK`; `hbn` and `hbo`, the $b\,i$ are orthonormal for the pairing $\int_{D}b\,i\cdot\overline{b\,j}$ over the canonical truncation domain $D$ against the adelic Haar measure; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid cls\,i=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ is exactly the isotypic cuspidal submodule of $\pi$ intersected with the type cut; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function at `pins` with character $\xi K$, continuous, invariant under right translation by the level group `pins.U N`, lying in the type cut, and orthogonal over $D$ to every $b\,i$, vanishes almost everywhere on $D$ for the restricted Haar measure.
--
--   **Eisenstein index family.** A countable type $\iota E$ and families $\mu,\nu:\iota E\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ are given, with hypotheses (all named with a leading underscore) that each $\mu\,e$, $\nu\,e$ is unitary, is an idele class character, is continuous, that $\mu\,e\cdot\nu\,e=\xi K$, and that distinct indices are separated on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16) (the kernel of the distributive Haar character).
--
--   **Induced sections and Eisenstein data for the index family.** Integers $nE\,e$ and sections $\varphi E\,e\,j\,s$ are given, with the hypotheses: each $\varphi E\,e\,j\,s$ is an induced section for the pair $\bigl(\mu\,e\cdot\alpha m^{\,s+1/2},\ \nu\,e\cdot\alpha m^{-(s+1/2)}\bigr)$, i.e. transforms by the product of these characters evaluated on the two diagonal entries of an adelic Borel element; is archimedean $K$-finite (finite-dimensional span of right translates under each archimedean row-isometry subgroup) and $K_f$-smooth; is jointly continuous in $(s,g)$ and holomorphic in $s$ for fixed $g$; has, at each infinite place, a single finite-dimensional space of $K$-types containing all translates, uniformly in $s$ and $g$; is flat on the maximal compact subgroup ($\varphi E\,e\,j\,s(k)=\varphi E\,e\,j\,0(k)$); is right invariant under $\mathrm{principalLevel}(N)\sqcap$ the finite-adelic subgroup; lies in the type cut; is orthonormal in $j$ over the maximal compact subgroup against `maximalCompactHaar K`; and spans (`_hφEspan`) all sections on each vertical line $s=it$ with the listed invariance and type properties. The hypothesis `_hpairs` states that any pair of unitary, continuous idele class characters with product $\xi K$ admitting a non-zero such section on a line $s=it$ agrees with some $(\mu\,e,\nu\,e)$ on the norm-one ideles. Further data $OE\,e\,j\subseteq\mathbb{C}$ and $EE,NE$ satisfy `_hEE` (nine clauses): $OE\,e\,j$ is open, preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; $s\mapsto EE\,e\,j\,s\,g$ and $s\mapsto NE\,e\,j\,s\,g$ are analytic on neighbourhoods in $OE\,e\,j$ for each $g$; both are continuous on $OE\,e\,j\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s>1/2$, $EE\,e\,j\,s\,g=\varphi E\,e\,j\,s\,g+\sum_{\xi\in K}\varphi E\,e\,j\,s\bigl(w\,u(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent with entry $\xi$; and for $\mathrm{Re}\,s>1/2$, $NE\,e\,j\,s\,g$ is the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi E\,e\,j\,s\,(w^{-1}u(x)g)\,dx$ against the adelic additive Haar measure.
--
--   **The two matched Paley–Wiener packages.** For $m=1,2$ the following data are given, in identical shape: a finite type $\iota P_m$; families $\mu P_m,\nu P_m$ of characters of the ideles, each unitary, each an idele class character, each continuous, with $\mu P_m\,e\cdot\nu P_m\,e=\xi K$ on the central subgroup `pins.Z`; a map $rP_m:\iota P_m\to\iota P_m$ swapping the two characters ($\mu P_m(rP_m\,e)=\nu P_m\,e$ and $\nu P_m(rP_m\,e)=\mu P_m\,e$); pairwise separation of distinct indices on the norm-one ideles; sections $\psi f_m\,e\,s$ which are induced sections for $\bigl(\mu P_m\,e\cdot\alpha m^{\,s+1/2},\ \nu P_m\,e\cdot\alpha m^{-(s+1/2)}\bigr)$, jointly continuous, entire in $s$, archimedean $K$-finite, $K_f$-smooth, with a uniform finite-dimensional space of $K$-types at each infinite place, right invariant under $\mathrm{principalLevel}(N)\sqcap$ the finite-adelic subgroup, and lying in the type cut; a rapid vertical decay hypothesis, namely for every $e$, $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C$ there is an integrable bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\lVert\psi f_m\,e\,(\sigma'+it)\,g\rVert\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$ and $g\in C$; a function $\psi_m$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which is a slab profile for `pins.Z` and $\xi K$ (measurable, invariant under left translation by adelic unipotents and by global Borel points, transforming by $\xi K$ under the centre, bounded on each slab $\lVert\det\rVert\in[d_1,d_2]$ with $d_1>0$, and supported in a height band $[a,b]$ with $a>0$ for the adelic height); the representation, for all $\sigma'\in\mathbb{R}$ and all $g$,
--   $$\psi_m(g)=\sum_{e\in\iota P_m}\frac{1}{4\pi}\int_{\mathbb{R}}\psi f_m\,e\,(\sigma'+it)\,g\,dt;$$
--   and matching maps $em_m:\iota P_m\to\iota E$, $\tau_m:\iota P_m\to\mathbb{R}$ with $\mu P_m\,i=\mu(em_m\,i)\cdot\lVert\cdot\rVert^{\,i\tau_m(i)}$ and $\nu P_m\,i=\nu(em_m\,i)\cdot\lVert\cdot\rVert^{-i\tau_m(i)}$, where $\lVert\cdot\rVert^{\,it}$ is [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22).
--
--   **Conclusion.** There exist a finite type $\iota P$, families $\mu P,\nu P:\iota P\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ with every $\mu P\,e$ and $\nu P\,e$ unitary and an idele class character and continuous, with $\mu P\,e\cdot\nu P\,e=\xi K$ on `pins.Z`, a swap map $rP$ with $\mu P(rP\,e)=\nu P\,e$ and $\nu P(rP\,e)=\mu P\,e$, pairwise separation of distinct indices on the norm-one ideles, and **two** section families $\varphi f,\psi f:\iota P\to\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ such that for each $e$ and $s$ both $\varphi f\,e\,s$ and $\psi f\,e\,s$ are induced sections for the same pair $\bigl(\mu P\,e\cdot\alpha m^{\,s+1/2},\ \nu P\,e\cdot\alpha m^{-(s+1/2)}\bigr)$, both families are jointly continuous in $(s,g)$ and entire in $s$ for each $g$, both are archimedean $K$-finite and $K_f$-smooth, both have a uniform finite-dimensional space of $K$-types at each infinite place, both satisfy the rapid vertical decay estimate in the form above (integrable bounded majorant for $(1+|t|)^n\lVert\cdot\rVert$, uniformly for $|\sigma'|\le\sigma_0$ and $g$ in a given compact set), both are right invariant under $\mathrm{principalLevel}(N)\sqcap$ the finite-adelic subgroup, and both lie in `archCutSubmodule K tysK`; together with matching maps $em:\iota P\to\iota E$ and $\tau:\iota P\to\mathbb{R}$ satisfying $\mu P\,i=\mu(em\,i)\cdot\lVert\cdot\rVert^{\,i\tau(i)}$ and $\nu P\,i=\nu(em\,i)\cdot\lVert\cdot\rVert^{-i\tau(i)}$; for which the two asserted conjuncts hold:
--
--   first, for all $\sigma'\in\mathbb{R}$ and all $g$,
--   $$\psi_1(g)=\sum_{e\in\iota P}\frac{1}{4\pi}\int_{\mathbb{R}}\varphi f\,e\,(\sigma'+it)\,g\,dt;$$
--   second, for all $\sigma'\in\mathbb{R}$ and all $g$,
--   $$\psi_2(g)=\sum_{e\in\iota P}\frac{1}{4\pi}\int_{\mathbb{R}}\psi f\,e\,(\sigma'+it)\,g\,dt.$$
--
--   Thus the two separately indexed Paley–Wiener representations are re-indexed over one common finite, swap-closed, separated and matched family of character pairs, the first profile being carried by $\varphi f$ and the second by $\psi f$.
--
--   This is the bookkeeping step in the continuous (Eisenstein) part of the spectral expansion which replaces two independently indexed matched Paley–Wiener representations of slab profiles by a single common index family carrying both section families. It is used by [`AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener), where the two profiles must be compared term by term over one index set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
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
      (ιP₁ : Type) [Fintype ιP₁]
      (μP₁ νP₁ : ιP₁ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₁ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₁ e)) (_hν₁ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₁ e))
      (_hμic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₁ e)) (_hνic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₁ e))
      (_hμc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₁ e x : ℂˣ) : ℂ))
      (_hμν₁ : ∀ (e : ιP₁)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₁ : ιP₁ → ιP₁) (_hr₁ : ∀ e, μP₁ (rP₁ e) = νP₁ e ∧ νP₁ (rP₁ e) = μP₁ e)
      (_hdist₁ : ∀ e e' : ιP₁, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₁ e x ≠ μP₁ e' x ∨ νP₁ e x ≠ νP₁ e' x)
      (ψf₁ : ιP₁ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₁ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₁ e) αm hαm s) (etaSnd (νP₁ e) αm hαm s) (ψf₁ e s))
      (_hψjc₁ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₁ e p.1 p.2))
      (_hψhol₁ : ∀ e g, Differentiable ℂ (fun s => ψf₁ e s g))
      (_hψK₁ : ∀ e s, IsArchKFinite K (ψf₁ e s)) (_hψsm₁ : ∀ e s, IsKfSmooth K (ψf₁ e s))
      (_hψKu₁ : ∀ (e : ιP₁) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₁ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₁ e x : ℂˣ) : ℂ))
      (_hψdec₁ : ∀ (e : ιP₁) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₁ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₁)
      (_hψrep₁ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₁ : ιP₁ → ιE) (τ₁ : ιP₁ → ℝ)
      (_hem₁ : ∀ i : ιP₁, μP₁ i = μ (em₁ i) * NumberField.TateGlobal.normPowChar K (τ₁ i) ∧
        νP₁ i = ν (em₁ i) * (NumberField.TateGlobal.normPowChar K (τ₁ i))⁻¹)
      (_hψlev₁ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₁ i s (g * u) = ψf₁ i s g)
      (_hψty₁ : ∀ i (s : ℂ), ψf₁ i s ∈ archCutSubmodule K tysK)
      (ιP₂ : Type) [Fintype ιP₂]
      (μP₂ νP₂ : ιP₂ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₂ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₂ e)) (_hν₂ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₂ e))
      (_hμic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₂ e)) (_hνic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₂ e))
      (_hμc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₂ e x : ℂˣ) : ℂ))
      (_hμν₂ : ∀ (e : ιP₂)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₂ : ιP₂ → ιP₂) (_hr₂ : ∀ e, μP₂ (rP₂ e) = νP₂ e ∧ νP₂ (rP₂ e) = μP₂ e)
      (_hdist₂ : ∀ e e' : ιP₂, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₂ e x ≠ μP₂ e' x ∨ νP₂ e x ≠ νP₂ e' x)
      (ψf₂ : ιP₂ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₂ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₂ e) αm hαm s) (etaSnd (νP₂ e) αm hαm s) (ψf₂ e s))
      (_hψjc₂ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₂ e p.1 p.2))
      (_hψhol₂ : ∀ e g, Differentiable ℂ (fun s => ψf₂ e s g))
      (_hψK₂ : ∀ e s, IsArchKFinite K (ψf₂ e s)) (_hψsm₂ : ∀ e s, IsKfSmooth K (ψf₂ e s))
      (_hψKu₂ : ∀ (e : ιP₂) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₂ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₂ e x : ℂˣ) : ℂ))
      (_hψdec₂ : ∀ (e : ιP₂) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₂)
      (_hψrep₂ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₂ : ιP₂ → ιE) (τ₂ : ιP₂ → ℝ)
      (_hem₂ : ∀ i : ιP₂, μP₂ i = μ (em₂ i) * NumberField.TateGlobal.normPowChar K (τ₂ i) ∧
        νP₂ i = ν (em₂ i) * (NumberField.TateGlobal.normPowChar K (τ₂ i))⁻¹)
      (_hψlev₂ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₂ i s (g * u) = ψf₂ i s g)
      (_hψty₂ : ∀ i (s : ℂ), ψf₂ i s ∈ archCutSubmodule K tysK),
    ∃ (ιP : Type) (_instP : Fintype ιP)
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
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hφK : ∀ e s, IsArchKFinite K (φf e s)) (_hφsm : ∀ e s, IsKfSmooth K (φf e s))
      (_hφKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf e s (g * u) = φf e s g)
      (_hφty : ∀ e (s : ℂ), φf e s ∈ archCutSubmodule K tysK)
      (_hψlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf e s (g * u) = ψf e s g)
      (_hψty : ∀ e (s : ℂ), ψf e s ∈ archCutSubmodule K tysK)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹),
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) := by sorry
