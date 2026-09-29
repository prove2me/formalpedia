-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq
-- name    : AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/9262d5ef-2106-51a9-a77b-1d83c1261d74
-- title:
--   Bessel inequality for Eisenstein coefficients of an automorphised test function
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring; $\mathrm{GL}_2(\mathbb{A}_K)$ carries the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, written $\mu$; and $D :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the canonical truncation domain attached to reals $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`). A set $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ occurs among the parameters but in no hypothesis and in no clause of the conclusion.
--
--   **Siegel covering data.** Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ are given, subject to `hcovK`: the union $\bigcup_{x\in T_K}\{y x\ :\ y\in \Sigma\}$ of the right translates of the centre-cut Siegel set $\Sigma=$ `centreCutSiegelSet K cK uK d₁K d₂K` satisfies `CoversModCentre`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z\in\mathbb{A}_K^\times$ with $\gamma g\,\mathrm{diag}(z,z)$ in that union. Here $\Sigma$ consists of those $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose local height at each infinite place $w$ is at least $c_K$, whose window quantity `xWindowSq` at each $w$ is at most $u_K^2$, and whose archimedean determinant norm at each $w$ lies in $[d_{1K},d_{2K}]$.
--
--   **Central measure data.** The group $\mathbb{A}_K^\times$ carries a measurable structure which is Borel for its topology, $\nu_{Z_K}$ is a Haar measure on it, and $\Omega_K$ is, by `hΩK`, a fundamental domain for the action of the image of $K^\times\to\mathbb{A}_K^\times$ with respect to $\nu_{Z_K}$.
--
--   **Character, level and type data.** $S_K$ is a finite set of finite places of $K$; $\xi_K$ is a homomorphism from the full subgroup $\top$ of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles, i.e. on the range of $K^\times\to\mathbb{A}_K^\times$ (`hξt`), and unitary, $|\xi_K(z)|=1$ for all $z$ (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and $\mathrm{tys}_K$ is an `ArchTypeFamily`, that is, a finite list `rep w i` of archimedean representations at each infinite place $w$. Finally $\alpha_m$ denotes the character $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the module character `distribHaarChar` of $\mathbb{A}_K$ composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and `hαm` asserts that $\alpha_m$ takes positive values.
--
--   Write $P$ for the carrier data `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: its domain is $D$, its measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is $\mu$, its central subgroup is all of $\mathbb{A}_K^\times$, its level subgroup at an ideal $M$ is `principalLevel (𝓞 K) K M` intersected with the kernel of `glArch` (the matrices trivial at the archimedean places), its Hecke generator at $v$ is `heckeGen (𝓞 K) K v`, and its measure on $\mathbb{A}_K$ is the additive Haar measure conditioned on the box `adelicBox K`. Write $A:=$ `archCutSubmodule K tysK`, the intersection over the infinite places $w$ of the sum of the type submodules attached to the representations $\mathrm{tys}_K.\mathrm{rep}\,w\,i$.
--
--   Under these hypotheses there exists $C\in\mathbb{R}$ with $C>0$ such that the following holds for all further data, $C$ being chosen before them.
--
--   **Cuspidal orthonormal data.** A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}_i$ over $\mathbb{C}$, subject to five hypotheses. `hb`: each $\mathrm{cls}_i$ lies in `cuspClasses K P ξK N SK`, i.e. has level $N$, has $a_v=b_v=0$ for $v\in S_K$, and has non-zero isotypic cuspidal submodule; and $b_i$ lies in `isotypicCuspSubmodule K P ξK N SK (cls i)` $\sqcap\,A$, the span of the $\mathrm{cls}_i$-isotypic smooth cuspidal automorphic functions for $P$ and $\xi_K$ (continuous, right invariant under the level group at $N$, Hecke eigen outside $S_K$ with the prescribed eigenvalues, and with the prescribed central eigenvalues), cut by the archimedean types. `hbn`: $\int_D b_i\overline{b_i}\,d\mu=1$. `hbo`: $\int_D b_i\overline{b_j}\,d\mu=0$ for $i\neq j$. `hbs`: for each cusp class $\pi$ the set $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly `isotypicCuspSubmodule K P ξK N SK π` $\sqcap\,A$. `hbc`: any $\varphi$ which is a smooth cuspidal automorphic function for $P$ and $\xi_K$, is continuous, is right invariant under the level group at $N$, lies in $A$, and satisfies $\int_D \varphi\,\overline{b_i}\,d\mu=0$ for all $i$, vanishes $\mu$-almost everywhere on $D$.
--
--   **Eisenstein family data.** A countable type $\iota_E$ and, for $e\in\iota_E$, characters $\mu_e,\nu_e:\mathbb{A}_K^\times\to\mathbb{C}^\times$ with: each unitary (`_hμ`, `_hν`), each trivial on $K^\times$ (`_hμic`, `_hνic`), each continuous (`_hμc`, `_hνc`), $\mu_e\nu_e=\xi_K$ (`_hμν`), and distinct parameters separated on the norm-one ideles: for $e\neq e'$ some $z$ in the kernel of `distribHaarChar` has $\mu_e z\neq\mu_{e'}z$ or $\nu_e z\neq\nu_{e'}z$ (`_hdist`). Further, integers $n_E(e)$ and sections $\varphi_{e,j}(s):\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ for $j<n_E(e)$ satisfying: $\varphi_{e,j}(s)$ is an induced section for the pair $\bigl(\mu_e\cdot\alpha_m^{\,s+1/2},\ \nu_e\cdot\alpha_m^{-(s+1/2)}\bigr)$, i.e. $\varphi(bg)$ equals the product of the two characters evaluated at the diagonal entries of $b$ times $\varphi(g)$ for $b$ in the adelic Borel subgroup (`_hφE`); archimedean $K$-finiteness (`_hφEK`); $K_f$-smoothness (`_hφEf`); joint continuity in $(s,g)$ (`_hφEjc`); holomorphy in $s$ for each $g$ (`_hφEhol`); for each infinite place $w$ a finite-dimensional space of functions on the row-isometry subgroup at $w$ containing all the functions $k\mapsto\varphi_{e,j}(s)(gk)$ (`_hφEKu`); flatness, $\varphi_{e,j}(s)=\varphi_{e,j}(0)$ on the maximal compact subgroup (`_hφEflat`); right invariance under `principalLevel (𝓞 K) K N` intersected with the kernel of `glArch` (`_hφElev`); membership in $A$ (`_hφEty`); orthonormality on the maximal compact, $\int \varphi_{e,i}(0)\overline{\varphi_{e,j}(0)}\,d(\mathrm{maximalCompactHaar}\ K)=\delta_{ij}$ (`_hφEon`); spanning on the unitary axis: every $\varphi_0$ which is an induced section for the pair attached to $(\mu_e,\nu_e)$ at $s=it$ and is continuous, archimedean $K$-finite, level invariant and in $A$, lies in the span of the $\varphi_{e,j}(it)$ (`_hφEspan`); and exhaustiveness of the parameter set (`_hpairs`): for every pair $(\mu',\nu')$ of continuous unitary characters trivial on $K^\times$ with $\mu'\nu'=\xi_K$, every $t\in\mathbb{R}$ and every non-zero $\varphi_0$ with the same five properties at $s=it$ for that pair, some $e$ satisfies $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   **Continuations.** Sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j}:\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ subject to `_hEE`, a conjunction of nine clauses: $O_{e,j}$ is open, preconnected, contains the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both $(s,g)\mapsto E_{e,j}(s)(g)$ and $(s,g)\mapsto N_{e,j}(s)(g)$ are continuous on $O_{e,j}\times\mathrm{univ}$; for $\mathrm{Re}\,s>1/2$, $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum'_{\xi\in K}\varphi_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u(\xi)$ the unipotent matrix with upper entry the image of $\xi$; and for $\mathrm{Re}\,s>1/2$, $N_{e,j}(s)(g)$ is the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi_{e,j}(s)(w^{-1}u(x)g)\,dx$ against the adelic additive Haar measure. The family $N_{e,j}$ enters only through `_hEE`.
--
--   **Test function.** A function $\Psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is measurable (`_hΨm`), vanishes outside some compact set (`_hΨc`) and is bounded in norm (`_hΨb`).
--
--   Set
--   $$\theta_\Psi(g)\ :=\ \sum^{\mathrm{f}}_{q\,\in\,\mathrm{GL}_2(K)/Z}\ \int_{\mathbb{A}_K^\times}\xi_K(w)^{-1}\,\bigl(\mathbf{1}_D\Psi\bigr)\bigl(\mathrm{diag}(w,w)\cdot(\gamma_q\, g)\bigr)\,d\nu_{Z_K}(w),$$
--   where the outer sum is the finitely supported sum over the quotient of $\mathrm{GL}_2(K)$ by its centre, $\gamma_q$ is the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of the chosen representative of $q$, $\mathrm{diag}(w,w)$ is `centralScalar`, and $\mathbf{1}_D\Psi$ is $\Psi$ restricted by the indicator of $D$; and set
--   $$\Theta_{e,j}(t)\ :=\ \int_D \theta_\Psi(g)\,\overline{E_{e,j}(it)(g)}\,d\mu(g)\qquad(t\in\mathbb{R}),$$
--   both written out in full in each clause of the Lean conclusion.
--
--   The conclusion is the conjunction of three assertions: first, for all $e$ and $j<n_E(e)$ the function $t\mapsto\Theta_{e,j}(t)$ belongs to $L^2(\mathbb{R})$ with respect to Lebesgue measure; second, the function $e\mapsto\int_{\mathbb{R}}\sum_{j<n_E(e)}|\Theta_{e,j}(t)|^2\,dt$ is summable on $\iota_E$; and third,
--   $$\sum_{e\in\iota_E}\ \int_{\mathbb{R}}\ \sum_{j<n_E(e)}\bigl|\Theta_{e,j}(t)\bigr|^2\,dt\ \le\ C\int_D\bigl|\theta_\Psi(g)\bigr|^2\,d\mu(g).$$
--
--   This is the Bessel inequality for the continuous (Eisenstein) part of the spectral decomposition on the truncation domain: the coefficients of the $\xi_K$-twisted central automorphisation of a bounded, compactly supported test function against the axis continuations of the Eisenstein families are square-integrable on the unitary axis, summable over the family of character pairs, and bounded by a constant multiple of the $L^2$-norm of that automorphisation on the domain. Its first two clauses provide exactly the square-integrability input for the Paley–Wiener coefficient statements downstream, and the inequality itself is used in the completeness and Lipschitz bounds for those coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq.lean

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

theorem AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq
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
    ∃ C : ℝ, 0 < C ∧
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
      (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
      (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
      (_hΨb : ∃ M : ℝ, ∀ y, ‖Ψ y‖ ≤ M),
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ =>
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2) ∧
    ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2
      ≤ C * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ‖(fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
