-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis
-- name    : AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/bdea56f6-7815-5788-8bdb-69585c4dac4c
-- title:
--   Weak wave-packet identity against pseudo-Eisenstein test series
-- statement:
--   Throughout, $K$ is a number field and $\mathbf{pins}$ abbreviates `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, i.e. the carrier data consisting of the Borel structure and Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2$ of the adeles, the domain $D :=$ `canonicalTruncationDomain K α β`, the full central subgroup $Z = \top$ of the idele units, the level subgroups $U(M) =$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v`, the Borel structure on the adeles and the additive adelic Haar measure conditioned on `adelicBox K`.
--
--   *Fixed data and hypotheses.* Reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K$ of adelic $2\times2$ matrices; reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K$ of adelic matrices, with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, and `hcovK`: the union $\bigcup_{x\in T_K}(\cdot\, x)$ of right translates of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` (finite part integral, all local heights $\ge c_K$, all window quantities $\le u_K^2$, all archimedean determinant norms in $[d_{1K},d_{2K}]$) satisfies `CoversModCentre`, that is, every $g$ can be carried into it by left multiplication by a global point and right multiplication by a central scalar. Further, a Haar measure $\nu_{Z_K}$ on the idele units and a set $\Omega_K$ that is a fundamental domain for the range of the principal ideles; a finite set $S_K$ of finite places; a character $\xi_K$ of the full subgroup $\top$ of idele units into $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles (`hξt`) and unitary (`hξu`); an ideal $N$ of $\mathcal O_K$ such that every finite place dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, whose associated submodule `archCutSubmodule K tysK` is the infimum over infinite places $w$ of the supremum of the finitely many archimedean type submodules at $w$.
--
--   Write $\alpha_m$ for the homomorphism from idele units to $\mathbb R^\times$ obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` by passing to real values and units, and assume `hαm`, that $\alpha_m$ takes positive values. The adeles carry the Borel $\sigma$-algebra.
--
--   *Assertion.* There exists $\kappa\in\mathbb R$ with $\kappa>0$ such that, for every choice of the following further data, the displayed integral vanishes. Since $\kappa$ is quantified before them, it depends only on the fixed data above.
--
--   (1) *Cuspidal basis.* A type $\iota$, functions $b_i$ on $\mathrm{GL}_2$ of the adeles and Hecke eigensystems $\mathrm{cls}_i$ over $\mathbb{C}$ such that: `hb`, each $\mathrm{cls}_i$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing Hecke and central data at the places of $S_K$, non-zero isotypic cusp submodule) and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}_i$ intersected with `archCutSubmodule K tysK`; `hbn` and `hbo`, the $b_i$ are orthonormal for the pairing $\int_D b_i\overline{b_j}$ against the adelic $\mathrm{GL}_2$ Haar measure; `hbs`, for every $\pi$ in `cuspClasses K pins ξK N SK` the fibre $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ over it is exactly the isotypic cusp submodule of $\pi$ intersected with the archimedean cut submodule; and `hbc`, completeness: any $\varphi$ which satisfies `IsSmoothCuspAutomorphicFnAt K pins ξK` (automorphic for the pins and central character $\xi_K$, cuspidal in the sense of the predicate `IsCuspidalFn` for the adelic measure and the unipotent embedding, and `IsKfSmooth`, a smooth vector for the finite adelic subgroup), is continuous, is right invariant under $U(N)$, lies in the archimedean cut submodule and is orthogonal on $D$ to every $b_i$, vanishes almost everywhere for the Haar measure restricted to $D$.
--
--   (2) *Continuous-spectrum frame.* A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to$ characters of the idele units, subject to the group of hypotheses (unitarity, triviality on $K^\times$ in the sense of `IsIdeleClassChar`, continuity of both families, $\mu_e\nu_e=\xi_K$ pointwise, and pairwise separation: distinct indices are distinguished by some norm-one idele). Integers $n_E(e)$ and section families $\varphi_{e,j}(s)$ subject to the group of hypotheses, summarised here: each $\varphi_{e,j}(s)$ is an induced section for the pair `etaFst (μ e) αm hαm s` $=\mu_e\,\alpha_m^{s+1/2}$, `etaSnd (ν e) αm hαm s` $=\nu_e\,\alpha_m^{-(s+1/2)}$ in the sense that $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; archimedean $K$-finite; $K_f$-smooth; jointly continuous in $(s,g)$; holomorphic in $s$ for each $g$; at each infinite place the right translates under `archRowIsometrySubgroup K w` lie in a fixed finite-dimensional space; flat, the value at $s$ on the maximal compact agreeing with the value at $0$; right invariant under $U(N)$; of the given archimedean types; orthonormal for $\int$ over `adelicMaximalCompact K` with `maximalCompactHaar K`; and spanning, in that for every $e$ and real $t$ every induced section at $it$ with these continuity, $K$-finiteness, level and type properties lies in the span of the $\varphi_{e,j}(it)$. The hypothesis `_hpairs` requires in addition that every pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'=\xi_K$ admitting a non-zero such section at some point $it$ is matched on the norm-one ideles by some $e\in\iota_E$.
--
--   (3) *Axis continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j}$ such that `_hEE` holds: $O_E(e,j)$ is open, preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; for each $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{univ}$ jointly; for $\mathrm{Re}\,s>1/2$, $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}\varphi_{e,j}(s)(w\,u(\xi)\,g)$ with $w$ the global Weyl element and $u$ the unipotent embedding, and $N_{e,j}(s)(g)$ equals the Weyl intertwining integral $\int \varphi_{e,j}(s)(w^{-1}u(x)g)$ against the additive adelic Haar measure.
--
--   (4) *Paley–Wiener datum $\psi$.* A finite type $\iota_P$, characters $\mu_P,\nu_P$ with the group of hypotheses of unitarity, idele class triviality, continuity of both families, $\mu_P(e)\nu_P(e)=\xi_K$ on $Z$, a swap $r_P$ interchanging $\mu_P$ and $\nu_P$, and pairwise separation on the norm-one ideles. Section families $\psi f_e(s)$ subject to the group of hypotheses: induced for `etaFst (μP e) αm hαm s`, `etaSnd (νP e) αm hαm s`; jointly continuous; holomorphic in $s$; archimedean $K$-finite and $K_f$-smooth; finite-dimensional $K$-isotypic behaviour at each infinite place; and vertical decay `_hψdec`, namely for every $e$, $n$, $\sigma_0$ and compact $C$ there is an integrable bounded majorant $m$ with $(1+|t|)^n\|\psi f_e(\sigma'+it)(g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$ and $g\in C$. A function $\psi$ satisfying `IsSlabProfile K ⊤ ξK` (measurable; invariant under left unipotent translation and under left multiplication by global Borel points; transforming by $\xi_K$ under the centre; bounded on determinant-norm slabs; supported in a band of adelic heights) together with `_hψrep`: for every $\sigma'$ and $g$, $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb R}\psi f_e(\sigma'+it)(g)\,dt$. Matching data $e(\cdot):\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb R$ with `_hem`: $\mu_P(i)=\mu_{e(i)}\cdot$`normPowChar K (τ i)` and $\nu_P(i)=\nu_{e(i)}\cdot$`normPowChar K (τ i)`$^{-1}$. Finally `_hψlev` and `_hψty`: each $\psi f_i(s)$ is right invariant under $U(N)$ and of the given archimedean types.
--
--   (5) *Residual projection.* A function $p_\psi$ with `_hpψ`, $p_\psi$ is `IsAutomorphicFnAt` for the pins and $\xi_K$; `_hpψc`, for every $\varepsilon>0$ there is $r$ in `residualSpan (𝓞 K) K ⊤ ξK` (the span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ with $\chi^2=\xi_K$ on $Z$) which is automorphic for the pins and satisfies $\|p_\psi-r\|_{L^2}<\varepsilon$ for the Haar measure restricted to $D$; and `_hpψo`, for every automorphic $h$ in that residual span, $\int_D(\theta_\psi-p_\psi)\overline h=0$, where $\theta_\psi:=$ `pseudoEisenstein K ψ`, $\theta_\psi(g)=\psi(g)+\sum_{b\in K}\psi(w\,u(b)\,g)$.
--
--   (6) *Enlarged Paley–Wiener datum $\psi'$.* A finite type $\iota_X$ with characters $\mu_X,\nu_X$ subject to the same group of hypotheses (unitarity, idele class triviality, continuity of both, product $\xi_K$ on $Z$, a swap $r_X$, pairwise separation within $\iota_X$), together with `_hdistPX`, every index of $\iota_P$ is separated from every index of $\iota_X$ by some norm-one idele, and matching data $e_X:\iota_X\to\iota_E$, $\tau_X$ as in (4). Section families $\psi f'_e(s)$ indexed by $\iota_P\oplus\iota_X$, induced for `etaFst (Sum.elim μP μX e) αm hαm s` and `etaSnd (Sum.elim νP νX e) αm hαm s`, with the same group of hypotheses as in (4): joint continuity, holomorphy in $s$, archimedean $K$-finiteness, $K_f$-smoothness, finite-dimensional $K$-isotypic behaviour, vertical decay, right invariance under $U(N)$ and membership of the archimedean cut submodule. A function $\psi'$ satisfying `IsSlabProfile K ⊤ ξK` with the representation $\psi'(g)=\sum_{e\in\iota_P\oplus\iota_X}(4\pi)^{-1}\int_{\mathbb R}\psi f'_e(\sigma'+it)(g)\,dt$ for every $\sigma'$ and $g$.
--
--   *Conclusion.* With $\mathbf K$ denoting `adelicMaximalCompact K` with its Haar measure and $\mu_{\mathrm{GL}}$ the adelic $\mathrm{GL}_2$ Haar measure,
--   $$\int_{D}\theta_{\psi'}(g)\,\overline{\Big(\theta_{\psi}(g)-p_\psi(g)-\kappa\sum_{i\in\iota_P}\int_{\mathbb R}\sum_{j=1}^{n_E(e(i))}\Big(\int_{\mathbf K}\psi f_i(it)(k)\,\overline{\varphi_{e(i),j}(i(t+\tau_i))(k)}\,dk\Big)\,E_{e(i),j}(i(t+\tau_i))(g)\,dt\Big)}\,d\mu_{\mathrm{GL}}=0,$$
--   where $\theta_{\psi'}=$ `pseudoEisenstein K ψ'` and the spectral parameters are the purely imaginary points $it$ and $i(t+\tau_i)$.
--
--   This is the paired, or weak, form of the one-term wave-packet identity on the truncated quotient: the defect $\theta_\psi-p_\psi-\kappa\cdot(\text{wave packet built from }\psi)$ is shown to be orthogonal on the canonical truncation domain to the pseudo-Eisenstein series attached to every Paley–Wiener datum living on an enlargement of the character family of $\psi$. It is used by [`AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener), which converts this family of orthogonality relations into an almost-everywhere identity for the defect.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_sub_residualProj_sub_mul_sum_integral_sum_inner_mul_axis_continuation_eq_zero_of_matched_paleyWiener_of_cuspBasis
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
          (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (ιX : Type) [Fintype ιX]
      (μX νX : ιX → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμX : ∀ e, IsUnitaryChar (𝓞 K) K (μX e)) (_hνX : ∀ e, IsUnitaryChar (𝓞 K) K (νX e))
      (_hμicX : ∀ e, IsIdeleClassChar (𝓞 K) K (μX e)) (_hνicX : ∀ e, IsIdeleClassChar (𝓞 K) K (νX e))
      (_hμcX : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μX e x : ℂˣ) : ℂ))
      (_hνcX : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νX e x : ℂˣ) : ℂ))
      (_hμνX : ∀ (e : ιX)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μX e (z : (AdeleRing (𝓞 K) K)ˣ) * νX e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rX : ιX → ιX) (_hrX : ∀ e, μX (rX e) = νX e ∧ νX (rX e) = μX e)
      (_hdistX : ∀ e e' : ιX, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μX e x ≠ μX e' x ∨ νX e x ≠ νX e' x)
      (_hdistPX : ∀ (i : ιP) (e : ιX), ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP i x ≠ μX e x ∨ νP i x ≠ νX e x)
      (emX : ιX → ιE) (τX : ιX → ℝ)
      (_hemX : ∀ e : ιX, μX e = μ (emX e) * NumberField.TateGlobal.normPowChar K (τX e) ∧
        νX e = ν (emX e) * (NumberField.TateGlobal.normPowChar K (τX e))⁻¹)
      (ψf' : ιP ⊕ ιX → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf' : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (Sum.elim μP μX e) αm hαm s) (etaSnd (Sum.elim νP νX e) αm hαm s) (ψf' e s))
      (_hψjc' : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf' e p.1 p.2))
      (_hψhol' : ∀ e g, Differentiable ℂ (fun s => ψf' e s g))
      (_hψK' : ∀ e s, IsArchKFinite K (ψf' e s)) (_hψsm' : ∀ e s, IsKfSmooth K (ψf' e s))
      (_hψKu' : ∀ (e : ιP ⊕ ιX) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf' e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψdec' : ∀ (e : ιP ⊕ ιX) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf' e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ' : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ' : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ')
      (_hψrep' : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ' g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf' e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψlev' : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf' i s (g * u) = ψf' i s g)
      (_hψty' : ∀ i (s : ℂ), ψf' i s ∈ archCutSubmodule K tysK),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        AutomorphicForm.pseudoEisenstein K ψ' g *
          conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g -
            (κ : ℂ) * ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
