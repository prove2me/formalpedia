-- Prove2me | Theorems.Thm_AutomorphicForm_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero
-- name    : AutomorphicForm.forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/e2e702d8-0ca0-54fe-b922-c87eb2a83b33
-- title:
--   Orthogonality extends from Paley–Wiener data to all slab profiles
-- statement:
--   Throughout, $K$ is a number field, $0<\alpha<\beta$ are reals, and $\mathrm{GL}_2(\mathbb{A}_K)$ denotes `AdelicGL2 (𝓞 K) K`, the group of invertible $2\times 2$ matrices over the adele ring. Write $\alpha_m$ for the homomorphism `αm` from the idele group $(\mathbb{A}_K)^\times$ to $\mathbb{R}^\times$ obtained from the module `distribHaarChar (AdeleRing (𝓞 K) K)` by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units, and let `hαm` be the hypothesis that $\alpha_m(x)>0$ for all $x$. All integrals over $\mathrm{GL}_2(\mathbb{A}_K)$ are against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on the Borel $\sigma$-algebra, and $\Phi_0 :=$ `canonicalTruncationDomain K α β`.
--
--   Auxiliary data, fixed but otherwise unconstrained by the conclusion: a set $\Phi_K$ of adelic matrices; reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K$ of adelic matrices with $0<c_K$, $0<d_{1K}<d_{2K}$, subject to `hcovK`, which asserts that $\bigcup_{x\in T_K}\{g x : g\in\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\}$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the rational points and the centre, in the sense of `CoversModCentre` (the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean components have local height at least $c_K$ and $x$-window square at most $u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$); a Haar measure $\nu_{Z_K}$ on the idele units together with a set $\Omega_K$ that is a fundamental domain for the image of $K^\times$ in the ideles; a finite set $S_K$ of primes of $\mathcal{O}_K$; and an ideal $N$ of $\mathcal{O}_K$ with `hN`: every prime dividing $N$ belongs to $S_K$. Further fixed: a homomorphism $\xi_K$ from the full subgroup $\top$ of the idele units to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles, i.e. on the image of $K^\times$ (`hξt`), and of absolute value $1$ everywhere (`hξu`); and an archimedean type family $\mathcal{T}_K :=$ `tysK`, giving at each infinite place $w$ finitely many representations of the row-isometry group, whose associated cut `archCutSubmodule K tysK` is the intersection over $w$ of the sums of the corresponding type submodules.
--
--   The continuous-spectrum frame. A countable index type $\iota_E$ is given together with families $\mu,\nu:\iota_E\to\mathrm{Hom}((\mathbb{A}_K)^\times,\mathbb{C}^\times)$ subject to: unitarity of each $\mu_e$ and $\nu_e$ (`IsUnitaryChar`: absolute value $1$ at every idele); triviality on $K^\times$ (`IsIdeleClassChar`); continuity of both families; the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all ideles $z$; and pairwise separation `_hdist`: distinct $e\neq e'$ are distinguished by some $z$ in [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16), the kernel of the module. Next, integers $n_e$ and sections $\varphi_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ for $j\in\{0,\dots,n_e-1\}$ are given, subject to the following hypotheses. `_hφE`: each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair of characters `etaFst (μ e) αm hαm s` $=\mu_e\cdot\alpha_m^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi(g)$ for all $b$ in the adelic Borel subgroup (lower-left entry zero). `_hφEK`: archimedean $K$-finiteness at every infinite place. `_hφEf`: smoothness as a vector for the finite adelic subgroup, the kernel of the archimedean projection. `_hφEjc`: joint continuity in $(s,g)$. `_hφEhol`: entirety in $s$ for fixed $g$. `_hφEKu`: for each $e,j$ and each infinite place $w$ a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup containing all the right-translation functions $k\mapsto\varphi_{e,j}(s,gk)$. `_hφEflat`: flatness, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in the adelic maximal compact subgroup. `_hφElev`: right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`. `_hφEty`: each $\varphi_{e,j}(s,\cdot)$ lies in the archimedean cut of $\mathcal{T}_K$. `_hφEon`: orthonormality at $s=0$ over the maximal compact subgroup with its Haar measure `maximalCompactHaar K`, $\int \varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,dk=\delta_{ij}$. `_hφEspan`: completeness on the unitary axis, namely every $\varphi_0$ which is an induced section for the characters at $s=it$ and is continuous, archimedean $K$-finite, invariant under the level group and in the archimedean cut lies in the complex span of the $\varphi_{e,j}(it,\cdot)$. `_hpairs`: exhaustion of pairs, namely for any continuous unitary idele class characters $\mu',\nu'$ with $\mu'\nu'=\xi_K$, any $t\in\mathbb{R}$ and any nonzero $\varphi_0$ which is an induced section for the corresponding pair at $s=it$ and satisfies the same continuity, $K$-finiteness, level and type conditions, there is an $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles. Finally, sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j},N_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ are given, with `_hEE` asserting, for each $e,j$: $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s>1/2$ one has $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}(s,w\,u(\xi)\,g)$ with $w=$ `adelicWeyl` and $u(\xi)$ the unipotent matrix with upper-right entry $\xi$; and for $\mathrm{Re}\,s>1/2$ one has $N_{e,j}(s,g)=\int_{\mathbb{A}_K}\varphi_{e,j}(s,w^{-1}u(x)g)\,dx$ against the additive Haar measure `adelicAddHaar`.
--
--   The test function. A function $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ is given with three hypotheses: `_hf`, that $f$ satisfies `IsAutomorphicFnAt` for the character $\xi_K$ and for the data package `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)` — that is, $f$ lies in the space cut out by the predicate `LsXiMember` for the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the domain $\Phi_0$, the central subgroup $\top$ with character $\xi_K$, the level groups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen`, and the conditioning set `adelicBox K`; `_hflev`, that $f$ is right invariant under the level group of those data at $N$; and `_hfty`, that $f$ lies in the archimedean cut of $\mathcal{T}_K$.
--
--   The orthogonality hypothesis `_horth`. For every finite index type $\iota_P$, every pair of families $\mu_P,\nu_P:\iota_P\to\mathrm{Hom}((\mathbb{A}_K)^\times,\mathbb{C}^\times)$ that are unitary, trivial on $K^\times$, continuous (the two continuity clauses `_hμc` and `_hνc`) and satisfy $\mu_P(e)(z)\,\nu_P(e)(z)=\xi_K(z)$ for all ideles $z$, every involution-like map $r_P:\iota_P\to\iota_P$ with $\mu_P(r_P e)=\nu_P(e)$ and $\nu_P(r_P e)=\mu_P(e)$, pairwise separation of the indices on the norm-one ideles, every family of sections $\psi_i(s,\cdot)$ which are induced sections for the pairs `etaFst (μP e) αm hαm s`, `etaSnd (νP e) αm hαm s`, jointly continuous, entire in $s$, archimedean $K$-finite, smooth for the finite adelic subgroup, uniformly $K$-finite in the sense of a finite-dimensional subspace $W$ as above, and rapidly decreasing in the sense of `_hψdec` (for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_e(\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$), and every $\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying `IsSlabProfile K ⊤ ξK ψ` (measurability; invariance under left translation by unipotent adelic matrices; invariance under left translation by rational Borel matrices; the central transformation law $\psi(z\cdot g)=\xi_K(z)\psi(g)$; boundedness on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$; and a height band, i.e. reals $a,b$ with $a>0$ such that the adelic height of any $g$ with $\psi(g)\neq 0$ lies in $[a,b]$), such that the wave-packet representation `_hψrep` holds: $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_e(\sigma'+it,g)\,dt$ for every real $\sigma'$ and every $g$, and such that there are maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot|\cdot|^{i\tau(i)}$ and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot|\cdot|^{-i\tau(i)}$ in terms of [`NumberField.TateGlobal.normPowChar`](def/NumberField_NormPowChar.html#L22), each $\psi_i(s,\cdot)$ being moreover right invariant under the level group at $N$ (`_hψlev`) and lying in the archimedean cut (`_hψty`) — for all such data,
--   $$\int_{\Phi_0}\big(\mathrm{pseudoEisenstein}\,K\,\psi\big)(g)\,\overline{f(g)}\,dg=0,$$
--   where `pseudoEisenstein K ψ` $(g)=\psi(g)+\sum_{\beta\in K}\psi(w\,u(\beta)\,g)$.
--
--   Conclusion. For every $\chi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying `IsSlabProfile K ⊤ ξK χ` (the six clauses just listed: measurability, unipotent invariance, rational Borel invariance, the central law with $\xi_K$, slab boundedness, and a height band with positive lower end),
--   $$\int_{\Phi_0}\big(\mathrm{pseudoEisenstein}\,K\,\chi\big)(g)\,\overline{f(g)}\,dg=0,$$
--   the integral being over the canonical truncation domain against `adelicGLHaar (Fin 2) (𝓞 K) K`. Thus orthogonality of $f$ to the pseudo-Eisenstein series of matched level-$N$ Paley–Wiener data propagates to the pseudo-Eisenstein series of an arbitrary slab profile.
--
--   This is the density step in the $L^2$ theory of pseudo-Eisenstein series for $\mathrm{GL}_2$ over a number field: Paley–Wiener data whose wave packets are matched to the fixed continuous-spectrum frame are $L^2$-dense among slab profiles on the truncation domain, so the vanishing of the inner product against a level-$N$, type-cut automorphic function $f$ extends from the matched family to all slab profiles. It feeds the one-term wave-packet representation [`AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero.lean

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

theorem AutomorphicForm.forall_isSlabProfile_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero
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
      (f : AdelicGL2 (𝓞 K) K → ℂ)
      (_hf : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f)
      (_hflev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, f (g * u) = f g)
      (_hfty : f ∈ archCutSubmodule K tysK)
      (_horth : ∀
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
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K ψ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (χ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hχ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK χ),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        AutomorphicForm.pseudoEisenstein K χ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
