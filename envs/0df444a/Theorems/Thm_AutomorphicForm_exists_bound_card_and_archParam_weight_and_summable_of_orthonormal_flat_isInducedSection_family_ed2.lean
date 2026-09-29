-- Prove2me | Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
-- name    : AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/5f2e2b2d-c4ed-5b1b-bea8-db3baa1a6575
-- title:
--   Uniform bounds, parameters and summability for GL(2) Eisenstein data
-- statement:
--   Let $K$ be a number field. The statement fixes the following data, in four groups.
--
--   *Siegel-covering data.* Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K$ of points of $\mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`); real parameters $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$; a finite set $T_K$ of adelic matrices; and the hypothesis `hcovK`, asserting that the union $\bigcup_{x\in T_K}\,(\,\cdot\,x)\bigl(\text{centreCutSiegelSet}(c_K,u_K,d_{1K},d_{2K})\bigr)$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g\,\mathrm{diag}(z,z)$ in that union; here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place $w$ has local height $\ge c_K$ and $x$-window $\mathrm{xWindowSq}\le u_K^2$, and whose archimedean determinant norm at each $w$ lies in $[d_{1K},d_{2K}]$.
--
--   *Measure data on the ideles.* A Haar measure $\nu_{Z_K}$ on $\mathbb{A}_K^\times$ and a set $\Omega_K$ which, by `hΩK`, is a fundamental domain for the action of the image of $K^\times$ under `Units.map (algebraMap K (AdeleRing (𝓞 K) K))`.
--
--   *Central character and level data.* A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top\le\mathbb{A}_K^\times$ to $\mathbb{C}^\times$, continuous as a function of the idele (`hξc`) and trivial on the image of $K^\times$ (`hξt`); an ideal $N$ of $\mathcal{O}_K$ such that every finite place dividing $N$ lies in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place $w$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$; functions $f_{aK}$ on $\mathrm{GL}_2$ of the infinite adeles and $f_{SK}$ on the local groups $\mathrm{GL}_2(K_v)$ with values in $\mathbb{C}$; and a real number $w$ with $\|\xi_K(z)\|=\lVert z\rVert^{w}$ for all $z$, where $\lVert\cdot\rVert$ is the idele norm `ideleNorm` given by the module character `distribHaarChar` (`hξw`).
--
--   Write $\alpha_m:\mathbb{A}_K^\times\to\mathbb{R}^\times$ for the idele norm viewed as a homomorphism of unit groups (the composite of `distribHaarChar` with $\mathbb{R}_{\ge 0}\to\mathbb{R}$), and use the Borel structure `adeleBorel` on the adeles.
--
--   The remaining hypotheses are universally quantified. They are: positivity $0<\alpha_m(x)$ for all $x$ (`hαm`); a countable index type $\iota_E$; families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ subject to the *character group*: each $\mu_e,\nu_e$ is unitary ($|\mu_e(x)|=1$, $|\nu_e(x)|=1$ for all $x$), each is an idele class character (trivial on $K^\times$), each is continuous, the product relation $\mu_e(z)\nu_e(z)\lVert z\rVert^{w}=\xi_K(z)$ holds for all $e$ and $z$, and the pairs are pairwise distinct on norm-one ideles: for $e\ne e'$ there is $z$ in the kernel of `distribHaarChar` with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$.
--
--   Next, a function $n_E:\iota_E\to\mathbb{N}$ and a family $\varphi_E$ assigning to each $e$, each $j\in\{0,\dots,n_E(e)-1\}$ and each $s\in\mathbb{C}$ a function on $\mathrm{GL}_2(\mathbb{A}_K)$, subject to the *section group*: each $\varphi_E(e,j,s)$ is an induced section for the pair $\bigl(\mu_e\cdot\alpha_m^{\,s+1/2},\ \nu_e\cdot\alpha_m^{-(s+1/2)}\bigr)$, i.e. $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $\mathbf{K}$-finite and $K_f$-smooth (its stabiliser in the kernel of `glArch` is open); the map $(s,g)\mapsto\varphi_E(e,j,s)(g)$ is continuous and $s\mapsto\varphi_E(e,j,s)(g)$ is entire; for each $e,j$ and each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at $w$ containing all the functions $k\mapsto\varphi_E(e,j,s)(gk)$; flatness holds, $\varphi_E(e,j,s)(k)=\varphi_E(e,j,0)(k)$ for $k$ in the adelic maximal compact subgroup; right invariance holds under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$; each $\varphi_E(e,j,s)$ lies in the archimedean cut submodule $\mathrm{archCutSubmodule}(\mathrm{tys}_K)$, the intersection over infinite places of the sum of the listed type submodules; orthonormality holds on the maximal compact subgroup, $\int \varphi_E(e,i,0)\overline{\varphi_E(e,j,0)}\,d(\mathrm{maximalCompactHaar})=\delta_{ij}$; a spanning property `_hφEspan`: for every $e$, every $t\in\mathbb{R}$ and every $\varphi_0$ which is an induced section for the pair attached to $(\mu_e,\nu_e)$ at $s=it$, is continuous, archimedean $\mathbf{K}$-finite, invariant under the above level subgroup and lies in the archimedean cut submodule, $\varphi_0$ lies in the complex span of the $\varphi_E(e,j,it)$, $j<n_E(e)$; and an exhaustiveness property `_hpairs`: for every pair $(\mu',\nu')$ of continuous unitary idele class characters satisfying the same product relation with $\xi_K$, every $t\in\mathbb{R}$ and every non-zero $\varphi_0$ with the same five properties at $s=it$, there is an index $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   Finally, *Eisenstein and intertwining data*: sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E,N_E$ of functions of $(s,g)$, subject to `_hEE` (ten clauses): each $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s)(g)$ and $s\mapsto N_E(e,j,s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both $(s,g)\mapsto E_E$ and $(s,g)\mapsto N_E$ are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\operatorname{Re}s>1/2$ one has the Bruhat expansion $E_E(e,j,s)(g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}\varphi_E(e,j,s)\bigl(\mathrm{adelicWeyl}\cdot u(\xi)\cdot g\bigr)$, with $u(\xi)$ the upper unipotent matrix with entry $\xi$; and $N_E(e,j,s)(g)=\int \varphi_E(e,j,s)\bigl(\mathrm{adelicWeyl}^{-1}u(x)g\bigr)\,d(\mathrm{adelicAddHaar})(x)$ for $\operatorname{Re}s>1/2$.
--
--   Under these hypotheses there exist a natural number $D$, families $\tau^\mu,\tau^\nu:\iota_E\to(\text{infinite places})\to\mathbb{R}$, families $m^\mu,m^\nu:\iota_E\to(\text{infinite places})\to\mathbb{Z}$, natural numbers $M_0$ and $n_\rho$, a finite list $\rho_1,\dots,\rho_{n_\rho}$ (indexed by $\mathrm{Fin}\,n_\rho$) of families of characters of the local unit groups $(K_v)^\times$ over the finite places $v$, and a natural number $B_0$, such that:
--
--   1. $n_E(e)\le D$ for every $e$.
--
--   2. For all $e$, every infinite place $v$ and every $x\in(K_v)^\times$ whose image under `extensionEmbedding` has positive real part and vanishing imaginary part, $\mu_e$ and $\nu_e$ have archimedean parameters: the local character $\mathrm{archLocalChar}(\mu_e)_v(x)$ equals $\lVert\mathrm{archUnitHom}_v(x)\rVert^{\,i\tau^\mu_e(v)}$ and $\mathrm{archLocalChar}(\nu_e)_v(x)$ equals $\lVert\mathrm{archUnitHom}_v(x)\rVert^{\,i\tau^\nu_e(v)}$, the norm being the idele norm of the idele with component $x$ at $v$ and $1$ elsewhere.
--
--   3. For all $e$, every infinite place $v$ and every $x\in(K_v)^\times$ whose image $z$ under `extensionEmbedding` has $\|z\|=1$: $\mathrm{archLocalChar}(\mu_e)_v(x)=z^{m^\mu_e(v)}$ and $\mathrm{archLocalChar}(\nu_e)_v(x)=z^{m^\nu_e(v)}$.
--
--   4. For every $e$ with $n_E(e)>0$ and every infinite place $v$: $|m^\mu_e(v)|\le M_0$ and $|m^\nu_e(v)|\le M_0$.
--
--   5. For every $e$ with $n_E(e)>0$: the character $\mu_e\nu_e^{-1}$ is unramified at every finite place $v\notin S_K$, in the sense that its local character is trivial on every $u\in(K_v)^\times$ with both $u$ and $u^{-1}$ integral; and there is an index $r\le n_\rho$ such that for all $v\in S_K$ and all such $u$ one has $\mathrm{localChar}(\mu_e\nu_e^{-1})_v(u)=\rho_r(v)(u)$.
--
--   6. For every $B\ge B_0$: for each $e$ the function $t\mapsto\bigl(1+\sum_v(|t+\tau^\mu_e(v)|+|t-\tau^\nu_e(v)|)\bigr)^{-B}$, the sum being over the infinite places, is integrable on $\mathbb{R}$; the family of integrals $\int_{\mathbb{R}}\bigl(1+\sum_v(|t+\tau^\mu_e(v)|+|t-\tau^\nu_e(v)|)\bigr)^{-B}\,dt$, set to $0$ when $n_E(e)=0$, is summable over $e$; and the family $\bigl(1+\sum_v(|\tau^\mu_e(v)|+|\tau^\nu_e(v)|)\bigr)^{-B}$, again set to $0$ when $n_E(e)=0$, is summable over $e$.
--
--   The bound $D$, the parameters, the weight bound $M_0$, the list $\rho$ and the exponent threshold $B_0$ are thus uniform in the Eisenstein data.
--
--   This is the uniformity statement for the continuous spectrum of $\mathrm{GL}_2$ over a number field $K$: a single dimension bound, a single bound on archimedean weights, a finite list of possible ramification data at the places of $S_K$, and a single exponent threshold beyond which the archimedean parameter profiles are integrable and summable over the family. It is used by the subsequent estimates on sums of Eisenstein series and their intertwining integrals over Siegel domains, in particular by the dominated-sum and integrability results for truncated Eisenstein contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family_ed2
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
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
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
      ,
    ∃ (D : ℕ) (τμ τν : ιE → InfinitePlace K → ℝ) (mμ mν : ιE → InfinitePlace K → ℤ) (M₀ : ℕ) (nρ : ℕ)
      (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (B₀ : ℕ),
      (∀ e, nE e ≤ D) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ e v : ℝ) : ℂ) * Complex.I) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν e v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v)) ∧
      (∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ) ∧ |mν e v| ≤ (M₀ : ℤ)) ∧
      (∀ e, 0 < nE e →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt (μ e * (ν e)⁻¹) v) ∧
        ∃ r : Fin nρ, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar (μ e * (ν e)⁻¹) v u = ρs r v u) ∧
      (∀ B : ℕ, B₀ ≤ B →
        (∀ e : ιE, MeasureTheory.Integrable
          (fun t : ℝ => (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)))) ∧
        Summable (fun e : ιE => if 0 < nE e then
          ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)) else 0) ∧
        Summable (fun e : ιE => if 0 < nE e then
          (1 + ∑ v : InfinitePlace K, (|τμ e v| + |τν e v|)) ^ (-(B : ℝ)) else 0)) := by sorry
