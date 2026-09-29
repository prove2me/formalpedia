-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact
-- name    : AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/f74a5a99-7528-504f-951b-807dff765c6c
-- title:
--   Summable integrable dominants for the GL₂ continuous spectral sum
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}$ its adele ring, and `AdelicGL2 (𝓞 K) K` denotes $GL_2(\mathbb{A})$. Write `pins` for the carrier data `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: its measurable space and measure on $GL_2(\mathbb{A})$ are the Borel structure and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, its domain is the canonical truncation domain `canonicalTruncationDomain K α β` (the third component of the canonically chosen truncation datum for the pair $(α, β)$), its central subgroup is all of $\mathbb{A}^\times$, its level subgroups are $M \mapsto \mathrm{principalLevel}(M) \cap \ker(\mathrm{glArch})$, its Hecke generators are the elements `heckeGen (𝓞 K) K v`, and its additive datum is the Borel structure on $\mathbb{A}$ together with `adelicAddHaar (𝓞 K) K` conditioned on the box `adelicBox K` (fundamental domain for the lattice at the infinite places times the integral finite adeles).
--
--   Geometric and measure-theoretic data. Real parameters $0 < α < β$; a set $ΦK \subseteq GL_2(\mathbb{A})$; Siegel parameters $cK, uK, d_{1K}, d_{2K}$ with $0 < cK$, $0 < d_{1K} < d_{2K}$, and a finite set $TK \subseteq GL_2(\mathbb{A})$ such that `hcovK` holds: the union $\bigcup_{x \in TK} (\cdot\, x)$-translates of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` (those $g$ whose finite part is integral, whose archimedean component at each infinite place has local height at least $cK$ and window square at most $uK^2$, and whose archimedean determinant norms lie in $[d_{1K}, d_{2K}]$) covers $GL_2(\mathbb{A})$ modulo the centre, i.e. every $g$ admits $γ \in GL_2(K)$ and $z \in \mathbb{A}^\times$ with $γ g \cdot \mathrm{diag}(z,z)$ in that union. A Haar measure $νZK$ on the idele units and a set $ΩK$ which, by `hΩK`, is a fundamental domain for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $νZK$.
--
--   Central character and level. A finite set $SK$ of finite places; a homomorphism $ξK$ from the full subgroup $\top \le \mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`), and unitary, $\|ξK(z)\| = 1$ for all $z$ (`hξu`); an ideal $N$ of $𝓞_K$ such that every finite place dividing $N$ lies in $SK$ (`hN`); and an archimedean type family $tysK$, consisting of a number `card w` of representations of the row-isometry subgroup at each infinite place $w$. The submodule `archCutSubmodule K tysK` is $\bigwedge_w \bigvee_{i < \mathrm{card}\, w}$ of the corresponding type submodules, and `archDualCutSubmodule K tysK` the analogous infimum of the dual type submodules.
--
--   The modulus character. Set $αm$ to be the composite of the distributive Haar character of $\mathbb{A}$ with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, viewed as a homomorphism $\mathbb{A}^\times \to \mathbb{R}^\times$; the Borel structure `adeleBorel (𝓞 K) K` is used on $\mathbb{A}$. The remaining data are quantified under the hypothesis `hαm` that $αm(x) > 0$ for all $x$.
--
--   Cuspidal orthonormal data. A type $ι$, functions $b : ι \to (GL_2(\mathbb{A}) \to \mathbb{C})$ and $cls : ι \to$ `HeckeEigensystem K ℂ` (each eigensystem carrying a nonzero level ideal and families of eigenvalues $a_v, b_v$), subject to: `hb`, that for each $i$ the eigensystem $cls\,i$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing $a_v$ and $b_v$ at all $v \in SK$, and nonzero isotypic cusp submodule) and $b\,i$ lies in the intersection of `isotypicCuspSubmodule K pins ξK N SK (cls i)` — the span of the continuous, $U(N)$-right-invariant, smooth cuspidal automorphic functions with central character $ξK$ whose Hecke and central eigenvalues are those of $cls\,i$ — with `archCutSubmodule K tysK`; `hbn`, normalisation $\int_{D} b\,i \cdot \overline{b\,i} = 1$ over the canonical truncation domain $D$ against the adelic Haar measure; `hbo`, orthogonality of $b\,i$ and $b\,j$ over $D$ for $i \neq j$; `hbs`, that for every cusp class $π$ the fibre $\{i \mid cls\,i = π\}$ is finite and the complex span of $b$ on that fibre equals the $π$-isotypic cusp submodule intersected with `archCutSubmodule K tysK`; and `hbc`, the completeness clause: any $φ$ which is a smooth cuspidal automorphic function for `pins` and $ξK$, continuous, right invariant under $U(N) = \mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$, a member of `archCutSubmodule K tysK`, and orthogonal over $D$ to every $b\,i$, vanishes almost everywhere on $D$.
--
--   Eisenstein parameter data. A countable type $ιE$ and families $μ, ν : ιE \to \mathrm{Hom}(\mathbb{A}^\times, \mathbb{C}^\times)$ with the hypotheses: `_hμ`, `_hν` (each $μ_e$, $ν_e$ unitary), `_hμic`, `_hνic` (each trivial on $K^\times$), `_hμc`, `_hνc` (continuity), `_hμν` ($μ_e(z)ν_e(z) = ξK(z)$ for all $e$, $z$), and `_hdist` (for $e \neq e'$ some $z$ in the norm-one ideles, the kernel of the distributive Haar character, has $μ_e(z) \neq μ_{e'}(z)$ or $ν_e(z) \neq ν_{e'}(z)$).
--
--   Sections. Integers $nE\,e$ and functions $φE\,e\,j : \mathbb{C} \to GL_2(\mathbb{A}) \to \mathbb{C}$ with the following clauses, each asserted for all $e$, $j$ and (where applicable) all $s$: `_hφE`, each $φE\,e\,j\,s$ is an induced section for the pair $\eta_1 = μ_e \cdot αm^{\,s+1/2}$, $\eta_2 = ν_e \cdot αm^{-(s+1/2)}$, that is $φ(bg) = \eta_1(b_{11})\eta_2(b_{22})φ(g)$ for $b$ in the adelic Borel subgroup; `_hφEK`, archimedean $K$-finiteness at every infinite place (finite-dimensional span of right translates under the archimedean row-isometry subgroup); `_hφEf`, smoothness as a vector for the finite adelic subgroup; `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, a single finite-dimensional subspace $W$ of functions on the row-isometry subgroup at each place $w$ containing all the restrictions $k \mapsto φE\,e\,j\,s(gk)$; `_hφEflat`, $φE\,e\,j\,s(k) = φE\,e\,j\,0(k)$ for $k$ in the adelic maximal compact subgroup (integral finite part, row-isometric archimedean components); `_hφElev`, right invariance under $\mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$; `_hφEty`, membership in `archCutSubmodule K tysK`; `_hφEon`, orthonormality $\int_{\mathbf{K}} φE\,e\,i\,0 \cdot \overline{φE\,e\,j\,0} = δ_{ij}$ against `maximalCompactHaar K`; `_hφEspan`, that for each $e$ and real $t$ every continuous, archimedean $K$-finite, level-$N$-right-invariant section of type $(\eta_1, \eta_2)$ at $s = it$ lying in `archCutSubmodule K tysK` lies in the span of the $φE\,e\,j(it)$; and `_hpairs`, that every pair of unitary, $K^\times$-trivial, continuous characters $μ', ν'$ with $μ'ν' = ξK$ admitting a nonzero such section at some point $it$ agrees with some $μ_e, ν_e$ on the norm-one ideles.
--
--   Continuation data. Sets $OE\,e\,j \subseteq \mathbb{C}$ and families $EE, NE$ with the hypothesis `_hEE` asserting, for each $e$ and $j$: $OE\,e\,j$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$, $s \mapsto EE\,e\,j\,s\,g$ and $s \mapsto NE\,e\,j\,s\,g$ are analytic on a neighbourhood of $OE\,e\,j$; both are continuous on $OE\,e\,j \times GL_2(\mathbb{A})$ jointly; and for $\mathrm{Re}\,s > 1/2$ one has $EE\,e\,j\,s\,g = φE\,e\,j\,s\,g + \sum_{ξ \in K}' φE\,e\,j\,s(w\,u(ξ)\,g)$ with $w$ the adelic Weyl element and $u(ξ)$ the unipotent matrix, and $NE\,e\,j\,s\,g$ equals the Weyl intertwining integral $\int_{\mathbb{A}} φE\,e\,j\,s(w^{-1}u(x)g)\,dx$ against `adelicAddHaar (𝓞 K) K`.
--
--   Test function. A function $f : GL_2(\mathbb{A}) \to \mathbb{C}$ which is continuous (`_hf`) and compactly supported (`_hfc`), and which is assumed factorizable ($f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ smooth in the archimedean matrix entries and compactly supported and $f_{\mathrm{fin}}$ locally constant and compactly supported), bi-invariant under $\mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$ (both $f(ug) = f(g)$ and $f(gu) = f(g)$), and archimedean bi-finite for $tysK$ (that is, $g \mapsto f(g^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`).
--
--   Conclusion. For every $x \in GL_2(\mathbb{A})$ and every compact set $C \subseteq GL_2(\mathbb{A})$ there exists a family $D : ιE \to \mathbb{R} \to \mathbb{R}$ such that: each $D\,e$ is integrable on $\mathbb{R}$; the family of integrals $e \mapsto \int_{\mathbb{R}} D\,e\,t\,dt$ is summable over $ιE$; and for all $e \in ιE$, all $t \in \mathbb{R}$ and all $y \in C$,
--   $$\Big\| \sum_{i,j < nE\,e} \Big( \int_{\mathbf{K}} \big(\mathrm{rightConv}\,(φE\,e\,j\,(it))\,f\big)(k)\,\overline{φE\,e\,i\,(it)(k)}\,d\,\mathrm{maximalCompactHaar}\Big) \cdot EE\,e\,i\,(it)(x)\,\overline{EE\,e\,j\,(it)(y)} \Big\| \le D\,e\,t,$$
--   where $\mathrm{rightConv}\,φ\,f\,(g) = \int_{GL_2(\mathbb{A})} φ(gz) f(z)\,dz$ against the adelic Haar measure and the inner integral is over the adelic maximal compact subgroup.
--
--   This is the absolute-convergence input for the continuous (Eisenstein) part of the spectral expansion of the kernel of a factorizable test function on $GL_2$ over a number field: it produces dominating functions for the inner double sum over the archimedean $K$-types, integrable in the spectral parameter $t$ and summable over the countable set of unitary character pairs, uniformly for the second variable in a compact set. It is used by [`AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT`](thm.html#AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT), and combines the coefficient decay for factorizable test functions, the uniform polynomial growth of unitary Eisenstein series on compacta, and the dimension and parameter-summability bounds for the Eisenstein data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact.lean

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

theorem AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_of_isCompact
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    (∀ (x : AdelicGL2 (𝓞 K) K) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ D : ιE → ℝ → ℝ, (∀ e, Integrable (D e)) ∧ (Summable fun e : ιE => ∫ t : ℝ, D e t) ∧
        ∀ (e : ιE) (t : ℝ), ∀ y ∈ C,
          ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
              (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
              (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y))‖ ≤ D e t) := by sorry
