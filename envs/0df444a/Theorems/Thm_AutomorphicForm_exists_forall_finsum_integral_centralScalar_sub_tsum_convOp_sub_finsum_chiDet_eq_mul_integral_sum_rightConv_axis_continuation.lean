-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_integral_sum_rightConv_axis_continuation
-- name    : AutomorphicForm.exists_forall_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_integral_sum_rightConv_axis_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/7f5ca3c7-0488-50b3-a219-0217f2ef5718
-- title:
--   Pointwise spectral identity for the GL₂ kernel on the unitary axis
-- statement:
--   Let $K$ be a number field, with $\mathbb{A}$ its adele ring and $G(\mathbb{A}) = \mathrm{GL}_2(\mathbb{A})$ written `AdelicGL2 (𝓞 K) K`. Fix reals $\alpha, \beta$ with $0 < \alpha$ (`hα`) and $\alpha < \beta$ (`hαβ`), and a set $\Phi_K$ of adelic matrices, which is subject to no hypothesis.
--
--   *Siegel covering data.* Reals $c_K, u_K, d_{1K}, d_{2K}$ and a finite set $T_K \subseteq G(\mathbb{A})$ are given, with $0 < c_K$, $0 < d_{1K}$, $d_{1K} < d_{2K}$, and `hcovK`: the union $\bigcup_{x \in T_K} (\cdot * x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` covers $G(\mathbb{A})$ modulo centre, in the sense of `CoversModCentre`: every $g$ admits $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,\mathrm{diag}(z,z)$ in that union. Here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components have local height $\ge c_K$ and window square $\le u_K^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_{1K}, d_{2K}]$.
--
--   *Central data.* The idele group $\mathbb{A}^\times$ carries a measurable structure which is the Borel one, $\nu_{ZK}$ is a Haar measure on $\mathbb{A}^\times$, and $\Omega_K$ is a fundamental domain (`IsFundamentalDomain`) for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_{ZK}$.
--
--   *Character, level and type data.* $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full subgroup $\top \le \mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles (`hξt`), and unitary, $|\xi_K(z)| = 1$ for all $z$ (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and $\mathrm{tys}_K$ is an `ArchTypeFamily K`, that is, a number $\mathrm{card}(w)$ of archimedean types at each infinite place $w$ together with finite-dimensional representations of the row-isometry group of $K_w$.
--
--   Writing $\alpha_m : \mathbb{A}^\times \to \mathbb{R}^\times$ for the unitisation of the module character `distribHaarChar (AdeleRing (𝓞 K) K)` composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and under the hypothesis `hαm` that $\alpha_m(x) > 0$ for all $x$, the assertion is the existence of a real $\kappa > 0$ — depending only on the data listed so far — such that the following holds for all further data.
--
--   *Cuspidal orthonormal system.* A type $\iota$, functions $b_i : G(\mathbb{A}) \to \mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i) \in$ `HeckeEigensystem K ℂ` are given, all spectral notions being taken for the carrier pins `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)` (Borel structure and Haar measure on $G(\mathbb{A})$, domain the canonical truncation domain of $(\alpha,\beta)$, central subgroup $\top$, level subgroups the principal levels intersected with the finite adelic subgroup, Hecke generators `heckeGen`, and the adele measure conditioned on `adelicBox K`), with central character $\xi_K$, level $N$ and bad set $S_K$. The hypotheses are: `hb`, each $\mathrm{cls}(i)$ is a cusp class (level $N$, vanishing Hecke and central parameters at the places of $S_K$, non-zero isotypic space) and each $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with `archCutSubmodule K tysK`; `hbn` and `hbo`, the $b_i$ are orthonormal for the inner product $\int_{\mathrm{canonicalTruncationDomain}} b_i \overline{b_j}$ against `adelicGLHaar`; `hbs`, for every cusp class $\pi$ the fibre $\{i \mid \mathrm{cls}(i) = \pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the isotypic cusp submodule of $\pi$ cut by the archimedean types; and `hbc`, the completeness hypothesis: any $\varphi$ which is a smooth cuspidal automorphic function for these pins and $\xi_K$ (automorphic and cuspidal, and $K_f$-smooth), continuous, invariant under right translation by `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, lying in `archCutSubmodule K tysK`, and orthogonal to every $b_i$ over the truncation domain, vanishes almost everywhere on the truncation domain.
--
--   *Eisenstein data.* A countable type $\iota_E$ and families $\mu, \nu : \iota_E \to \mathrm{Hom}(\mathbb{A}^\times, \mathbb{C}^\times)$ are given, with the hypotheses (all for each $e$) that $\mu_e, \nu_e$ are unitary, trivial on $K^\times$, continuous, satisfy $\mu_e(z)\nu_e(z) = \xi_K(z)$ for all $z$, and are pairwise distinct on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16) (`_hdist`).
--
--   For each $e$ a number $n_E(e)$ and a family $\varphi_{e,j}(s,\cdot)$, $j \in \mathrm{Fin}(n_E(e))$, of functions on $G(\mathbb{A})$ is given, subject to the following hypotheses. `_hφE`: $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair `etaFst (μ e) αm hαm s` $= \mu_e \cdot \alpha_m^{\,s+1/2}$ and `etaSnd (ν e) αm hαm s` $= \nu_e \cdot \alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg) = \eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup. `_hφEK`, `_hφEf`: each section is archimedean $K$-finite and $K_f$-smooth. `_hφEjc`, `_hφEhol`: joint continuity in $(s,g)$ and holomorphy in $s$ for each $g$. `_hφEKu`: at each infinite place $w$ there is a finite-dimensional subspace of functions on `archRowIsometrySubgroup K w` containing all right translates of every $\varphi_{e,j}(s,\cdot)$ along that subgroup. `_hφEflat`: flatness, $\varphi_{e,j}(s,k) = \varphi_{e,j}(0,k)$ for $k$ in `adelicMaximalCompact K`. `_hφElev`: right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`. `_hφEty`: membership in `archCutSubmodule K tysK`. `_hφEon`: orthonormality on the maximal compact, $\int \varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,d(\mathrm{maximalCompactHaar}\,K) = \delta_{ij}$. `_hφEspan`: for each $e$ and each real $t$, every induced section for the pair at $s = it$ which is continuous, archimedean $K$-finite, right invariant under the level subgroup and of the prescribed archimedean types lies in the span of the $\varphi_{e,j}(it,\cdot)$. `_hpairs`: conversely, for every pair $(\mu',\nu')$ of continuous unitary characters trivial on $K^\times$ with $\mu'\nu' = \xi_K$ admitting a non-zero such section at some $s = it$, there is an $e$ with $\mu_e = \mu'$ and $\nu_e = \nu'$ on the norm-one ideles.
--
--   Finally, sets $O_E(e,j) \subseteq \mathbb{C}$ and families $E_E(e,j,s,\cdot)$, $N_E(e,j,s,\cdot)$ are given, with the nine-clause hypothesis `_hEE`: $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ both $s \mapsto E_E(e,j,s,g)$ and $s \mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j) \times G(\mathbb{A})$; and for $\mathrm{Re}\,s > 1/2$ one has $E_E(e,j,s,g) = \varphi_{e,j}(s,g) + \sum_{\zeta \in K}' \varphi_{e,j}(s, w\, u(\zeta)\, g)$ with $w$ the adelic Weyl element and $u(\zeta)$ the unipotent matrix of $\zeta$, and $N_E(e,j,s,g) =$ `weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g`.
--
--   *Test function.* $f : G(\mathbb{A}) \to \mathbb{C}$ is continuous with compact support, factorizable (`IsFactorizableTestFn`: $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ smooth of compact support in the mixed-space entries and $f_{\mathrm{fin}}$ locally constant of compact support), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for $\mathrm{tys}_K$ (i.e. $x \mapsto f(x^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`).
--
--   The conclusion holds for all $x, y \in G(\mathbb{A})$ and consists of three conjuncts. Throughout write
--   $$A_e(t) \;=\; \sum_{i,j} \Big(\int_{\mathrm{adelicMaximalCompact}} (\mathrm{rightConv}\,\varphi_{e,j}(it,\cdot)\, f)(k)\,\overline{\varphi_{e,i}(it,k)}\; d(\mathrm{maximalCompactHaar}\,K)\Big)\, E_E(e,i,it,x)\,\overline{E_E(e,j,it,y)},$$
--   the sums being over $i, j \in \mathrm{Fin}(n_E(e))$ and $\mathrm{rightConv}\,\varphi\, f(g) = \int \varphi(gh) f(h)$ against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`.
--
--   First, for every $e$ the function $t \mapsto A_e(t)$ is integrable on $\mathbb{R}$. Secondly, $e \mapsto \int_{\mathbb{R}} \|A_e(t)\|\,dt$ is summable over $\iota_E$. Thirdly, the identity
--   $$\mathcal{K}^{\mathrm{fold}}(x,y) - \mathcal{K}^{\mathrm{cusp}}(x,y) - \mathcal{K}^{\mathrm{res}}(x,y) \;=\; \kappa \sum_{e \in \iota_E}' \int_{\mathbb{R}} A_e(t)\,dt$$
--   holds, where
--   $$\mathcal{K}^{\mathrm{fold}}(x,y) = \sum^{\mathrm{f}}_{q \in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))} \int_{\mathbb{A}^\times} \xi_K(z)\, f\big(x^{-1}\,\gamma_{q}\,(\mathrm{diag}(z,z)\,y)\big)\, d\nu_{ZK}(z)$$
--   with $\gamma_q$ the image in $G(\mathbb{A})$ of a chosen representative `q.out` of the coset $q$ and $\sum^{\mathrm{f}}$ the finitely-supported sum;
--   $$\mathcal{K}^{\mathrm{cusp}}(x,y) = V \cdot \sum_{i \in \iota}' (\mathrm{convOp}\,f\,b_i)(x)\,\overline{b_i(y)}, \qquad V = \nu_{ZK}\big(\Omega_K \cap \{z \mid \mathrm{ideleNorm}(\det \mathrm{diag}(z,z)) \in [\alpha,\beta]\}\big)$$
--   (as a real number, then a complex one), with $\mathrm{convOp}\,f\,u = \mathrm{rightConv}\,u\,f$; and
--   $$\mathcal{K}^{\mathrm{res}}(x,y) = \frac{V}{\mathrm{vol}(\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta)} \sum^{\mathrm{f}}_{\chi} \Big(\int f(g)\,\chi(\det g)\, d(\mathrm{adelicGLHaar})\Big)\,\chi(\det x)\,\chi^{-1}(\det y),$$
--   the volume in the denominator being that of the canonical truncation domain for `adelicGLHaar (Fin 2) (𝓞 K) K`, and the finitely-supported sum running over those characters $\chi$ of $\mathbb{A}^\times$ with $\chi(z)^2 = \xi_K(z)$ for all $z$ (`SquaresToXi`), trivial on the principal ideles, and continuous.
--
--   The identity is asserted pointwise, for every pair $(x,y)$, not merely almost everywhere on a product of truncation domains, and the constant $\kappa$ is uniform in the cuspidal system, the Eisenstein data, the test function and the points.
--
--   This is the pointwise form of the spectral expansion of the continuous (Eisenstein) part of the automorphic kernel for $\mathrm{GL}_2$ over a number field with unitary central character: after the geometric kernel has been folded over the centre and the cuspidal and residual kernels subtracted, the remainder equals, up to a universal positive constant, the integral over the unitary axis of the Eisenstein kernels attached to the pairs $(\mu_e,\nu_e)$. It is obtained from the corresponding almost-everywhere identity on the truncation domain by the vanishing principle for continuous $\mathrm{GL}_2(K)$-invariant kernels, and is used in turn by the two statements that smooth the identity against a weight $\lambda_T$ in the slab parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_integral_sum_rightConv_axis_continuation.lean

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

theorem AutomorphicForm.exists_forall_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_integral_sum_rightConv_axis_continuation
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (x y : AdelicGL2 (𝓞 K) K),
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)))) ∧
      (Summable fun e : ιE => ∫ t : ℝ, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y))‖) ∧
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK) -
        (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y)) -
        (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y)) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y)) := by sorry
