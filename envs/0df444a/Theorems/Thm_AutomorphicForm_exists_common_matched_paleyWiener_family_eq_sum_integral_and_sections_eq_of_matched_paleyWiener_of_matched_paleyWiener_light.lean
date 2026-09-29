-- Prove2me | Theorems.Thm_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_and_sections_eq_of_matched_paleyWiener_of_matched_paleyWiener_light
-- name    : AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_and_sections_eq_of_matched_paleyWiener_of_matched_paleyWiener_light
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/5ababf66-e260-59d7-b013-73c075ac23f0
-- title:
--   A common matched Paley–Wiener family carrying two section families
-- statement:
--   Throughout, $K$ is a number field; $\alpha,\beta$ are real with $0<\alpha$ and $\alpha<\beta$; $\Phi_K$ is a set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`), carried along without any hypothesis attached to it.
--
--   **Geometric and measure-theoretic frame.** Real parameters $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ are given, with $0<c_K$, $0<d_{1K}$ and $d_{1K}<d_{2K}$, and `hcovK` asserts `CoversModCentre` for the union $\bigcup_{x\in T_K}(\,\cdot\,x)\,[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,]$: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central idele $z$ with $\gamma g z$ in that union, the Siegel set consisting of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c_K\le$ `localHeight` and `xWindowSq` $\le u_K^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$. Further, $\nu_{ZK}$ is a Haar measure on the idele units $\mathbb{A}_K^\times$ and $\Omega_K$ is a fundamental domain (`IsFundamentalDomain`) for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{ZK}$.
--
--   **Central character, level, types.** $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the top subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$, continuous (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ such that every prime dividing $N$ belongs to $S_K$ (`hN`); and $\mathrm{tys}_K$ is an `ArchTypeFamily K`, i.e. a finite list of representations of the row-isometry subgroup at each infinite place. The character $\alpha_m:\mathbb{A}_K^\times\to\mathbb{R}^\times$ is the modulus character obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and $h_{\alpha m}$ asserts that $\alpha_m(x)>0$ for all $x$. For a character $\mu$ and $s\in\mathbb{C}$, `etaFst` $\mu\,\alpha_m\,h_{\alpha m}\,s=\mu\cdot\alpha_m^{\,s+1/2}$ and `etaSnd` $\nu\,\alpha_m\,h_{\alpha m}\,s=\nu\cdot\alpha_m^{-(s+1/2)}$, and `IsInducedSection` for a pair of characters means $\varphi(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup.
--
--   **The Eisenstein index family.** A countable type $\iota_E$ is given together with characters $\mu_e,\nu_e$ of $\mathbb{A}_K^\times$ satisfying: each is unitary (`IsUnitaryChar`) and trivial on $K^\times$ (`IsIdeleClassChar`), each is continuous, $\mu_e\nu_e=\xi_K$ pointwise, and distinct indices are separated on the norm-one ideles (`_hdist`: the kernel of `distribHaarChar` contains a point where $\mu$ or $\nu$ differ). For each $e$ there are $n_E(e)\in\mathbb{N}$ and functions $\varphi_{E}(e,j):\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, $j\in\mathrm{Fin}(n_E(e))$, subject to the following hypotheses: for all $e,j,s$ the function $\varphi_E(e,j,s)$ is an induced section for $(\,$`etaFst`$(\mu_e)(s),\,$`etaSnd`$(\nu_e)(s))$, satisfies `IsArchKFinite K` (at each infinite place $w$, `RightTranslatesSpanFinite` for `archRowIsometrySubgroup K w`) and `IsKfSmooth K` (a smooth vector for right translation by `finiteAdelicGL2Subgroup K`, the kernel of `glArch`); the map $(s,g)\mapsto\varphi_E(e,j,s,g)$ is continuous and $s\mapsto\varphi_E(e,j,s,g)$ is entire; for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K w` containing all right translates $k\mapsto\varphi_E(e,j,s,gk)$, uniformly in $s$ and $g$ (`_hφEKu`); on the maximal compact subgroup the sections are independent of $s$, $\varphi_E(e,j,s,k)=\varphi_E(e,j,0,k)$ (`_hφEflat`); they are right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`) and lie in `archCutSubmodule K tysK`, the intersection over infinite places of the span of the prescribed isotypic submodules (`_hφEty`); the system is orthonormal at $s=0$ for `maximalCompactHaar K`, $\int_{k}\varphi_E(e,i,0,k)\overline{\varphi_E(e,j,0,k)}=\delta_{ij}$ (`_hφEon`); it spans (`_hφEspan`): any $\varphi_0$ which is an induced section for the parameters $\mu_e,\nu_e$ at $s=it$, continuous, arch-$K$-finite, level-$N$ right invariant and of the prescribed types, lies in the complex span of the $\varphi_E(e,j,it)$; and the family is exhaustive (`_hpairs`): for every pair $\mu',\nu'$ of continuous unitary idele-class characters with $\mu'\nu'=\xi_K$ and every nonzero section $\varphi_0$ at $s=it$ with the same induced, continuity, arch-$K$-finiteness, level and type properties, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   **Continuation data.** Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j),N_E(e,j)$ of $(s,g)$ are given, with `_hEE` (nine clauses) asserting: $O_E(e,j)$ is open and preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; for each $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; and for $\mathrm{Re}\,s>1/2$ one has $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E\bigl(e,j,s,\,w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u$ the unipotent embedding, and $N_E(e,j,s,g)=$ `weylIntertwiningIntegral` of $\varphi_E(e,j,s)$ at $g$ for the adelic additive Haar measure, i.e. $\int\varphi_E(e,j,s,w^{-1}u(x)g)\,dx$.
--
--   **The two matched Paley–Wiener data.** For $k=1,2$ a finite type $\iota_{P_k}$ is given with characters $\mu_{P_k},\nu_{P_k}$, a map $r_{P_k}:\iota_{P_k}\to\iota_{P_k}$, a section family $\psi_{f_k}$, a function $\psi_k$ on $\mathrm{GL}_2(\mathbb{A}_K)$, and maps $e_{m_k}:\iota_{P_k}\to\iota_E$, $\tau_k:\iota_{P_k}\to\mathbb{R}$. The hypotheses, identical in shape for $k=1$ and $k=2$, are: $\mu_{P_k}(e),\nu_{P_k}(e)$ are unitary, idele-class and continuous; $\mu_{P_k}(e)(z)\nu_{P_k}(e)(z)=\xi_K(z)$ for all $z$ in the subgroup $Z$ of `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, which is the top subgroup of $\mathbb{A}_K^\times$; $r_{P_k}$ interchanges $\mu_{P_k}$ and $\nu_{P_k}$; distinct indices are separated on the norm-one ideles; each $\psi_{f_k}(e,s)$ is an induced section for $(\,$`etaFst`$(\mu_{P_k}(e))(s),\,$`etaSnd`$(\nu_{P_k}(e))(s))$, jointly continuous in $(s,g)$, entire in $s$, arch-$K$-finite, `IsKfSmooth`, uniformly of finite $K$-type at each infinite place, right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and a member of `archCutSubmodule K tysK`; a Paley–Wiener decay bound holds (`_hψdec`$_k$): for every $e$, $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C$ there is an integrable $m:\mathbb{R}\to\mathbb{R}$, bounded above, with $(1+|t|)^n\|\psi_{f_k}(e,\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$ and $g\in C$; $\psi_k$ satisfies `IsSlabProfile K Z ξK` (measurability, left invariance under unipotent adelic matrices and under global Borel points, central transformation by $\xi_K$, boundedness on determinant-norm slabs, and a height band for its support); the wave-packet representation $\psi_k(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_{f_k}(e,\sigma'+it,g)\,dt$ holds for every $\sigma'\in\mathbb{R}$ and every $g$; and the matching relations $\mu_{P_k}(i)=\mu_{e_{m_k}(i)}\cdot\|\cdot\|^{\,i\tau_k(i)}$, $\nu_{P_k}(i)=\nu_{e_{m_k}(i)}\cdot\|\cdot\|^{-i\tau_k(i)}$ hold, where $\|\cdot\|^{\,it}$ denotes [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22).
--
--   **Conclusion.** There exist a finite type $\iota_P$, characters $\mu_P,\nu_P:\iota_P\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$, a map $r_P:\iota_P\to\iota_P$, two section families $\varphi_f,\psi_f:\iota_P\to\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, maps $e_m:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$, and maps $j_1:\iota_{P_1}\to\iota_P$, $j_2:\iota_{P_2}\to\iota_P$, such that:
--
--   (a) each $\mu_P(e),\nu_P(e)$ is unitary, idele-class and continuous, $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for all $z$ in the subgroup $Z$ of the same `productionPinsOf` datum (the top subgroup), $r_P$ interchanges $\mu_P$ and $\nu_P$, and distinct indices of $\iota_P$ are separated on the norm-one ideles;
--
--   (b) for every $e$ and $s$ both $\varphi_f(e,s)$ and $\psi_f(e,s)$ are induced sections for $(\,$`etaFst`$(\mu_P(e))(s),\,$`etaSnd`$(\nu_P(e))(s))$; both families are jointly continuous in $(s,g)$ and entire in $s$ for fixed $g$; both are arch-$K$-finite, `IsKfSmooth`, and uniformly of finite $K$-type at each infinite place in the sense of the subspace clause above; both satisfy the Paley–Wiener decay bound with integrable bounded majorants as in `_hψdec`$_k$; and both are right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and lie in `archCutSubmodule K tysK`;
--
--   (c) the matching relations $\mu_P(i)=\mu_{e_m(i)}\cdot\|\cdot\|^{\,i\tau(i)}$ and $\nu_P(i)=\nu_{e_m(i)}\cdot\|\cdot\|^{-i\tau(i)}$ hold for all $i\in\iota_P$;
--
--   (d) $j_1$ and $j_2$ are injective and their images together cover $\iota_P$; on the image of $j_1$ the data are those of the first family, $\mu_P(j_1 i)=\mu_{P_1}(i)$, $\nu_P(j_1 i)=\nu_{P_1}(i)$, $e_m(j_1 i)=e_{m_1}(i)$, $\tau(j_1 i)=\tau_1(i)$ and $r_P(j_1 i)=j_1(r_{P_1} i)$; on the image of $j_2$ only the matching and the swap are transported, $e_m(j_2 i')=e_{m_2}(i')$ and $r_P(j_2 i')=j_2(r_{P_2} i')$;
--
--   (e) the sections are recorded explicitly: $\varphi_f(j_1 i,s,g)=\psi_{f_1}(i,s,g)$ for all $i,s,g$, and $\varphi_f(e,s,g)=0$ whenever $e$ is not in the image of $j_1$; while $\psi_f(j_2 i',s,g)=\psi_{f_2}\bigl(i',\,s+i(\tau(j_2 i')-\tau_2(i')),\,g\bigr)$, and $\psi_f(e,s,g)=0$ whenever $e$ is not in the image of $j_2$;
--
--   and, finally, the asserted proposition is the conjunction of the two wave-packet representations over the single index set $\iota_P$: for every $\sigma'\in\mathbb{R}$ and every $g\in\mathrm{GL}_2(\mathbb{A}_K)$,
--   $$\psi_1(g)=\sum_{e\in\iota_P}\frac{1}{4\pi}\int_{\mathbb{R}}\varphi_f(e,\sigma'+it,g)\,dt,\qquad \psi_2(g)=\sum_{e\in\iota_P}\frac{1}{4\pi}\int_{\mathbb{R}}\psi_f(e,\sigma'+it,g)\,dt.$$
--
--   This is the bookkeeping step in the continuous part of the spectral analysis of $\mathrm{GL}_2$ over a number field which replaces two separately indexed matched Paley–Wiener wave packets by a single finite, swap-closed, separated family of principal-series parameters, recording both section families explicitly together with the embeddings of the two original index sets and the imaginary parameter shift needed to re-house the second family. It is used by [`AutomorphicForm.forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_sum_extension_setIntegral_pseudoEisenstein_mul_conj_eq_zero`](thm.html#AutomorphicForm.forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_sum_extension_setIntegral_pseudoEisenstein_mul_conj_eq_zero), where the two profiles must be expanded over one and the same index set before their pairings with pseudo-Eisenstein series can be compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_and_sections_eq_of_matched_paleyWiener_of_matched_paleyWiener_light.lean

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

theorem AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_and_sections_eq_of_matched_paleyWiener_of_matched_paleyWiener_light
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
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (j₁ : ιP₁ → ιP) (j₂ : ιP₂ → ιP)
      (_hj₁ : Function.Injective j₁) (_hj₂ : Function.Injective j₂)
      (_hcov : ∀ e : ιP, (∃ i, j₁ i = e) ∨ (∃ i', j₂ i' = e))
      (_hj₁v : ∀ i, μP (j₁ i) = μP₁ i ∧ νP (j₁ i) = νP₁ i ∧ em (j₁ i) = em₁ i ∧ τ (j₁ i) = τ₁ i ∧
        rP (j₁ i) = j₁ (rP₁ i))
      (_hj₂v : ∀ i', em (j₂ i') = em₂ i' ∧ rP (j₂ i') = j₂ (rP₂ i'))
      (_hφv : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K), φf (j₁ i) s g = ψf₁ i s g)
      (_hφ0 : ∀ e : ιP, (∀ i, j₁ i ≠ e) → ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), φf e s g = 0)
      (_hψv : ∀ i' (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ψf (j₂ i') s g = ψf₂ i' (s + ((τ (j₂ i') - τ₂ i' : ℝ) : ℂ) * Complex.I) g)
      (_hψ0 : ∀ e : ιP, (∀ i', j₂ i' ≠ e) → ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ψf e s g = 0),
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) := by sorry
