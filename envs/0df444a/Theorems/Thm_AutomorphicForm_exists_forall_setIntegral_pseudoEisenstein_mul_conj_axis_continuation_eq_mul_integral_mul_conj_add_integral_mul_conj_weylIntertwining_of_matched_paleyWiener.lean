-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a434e692-750d-578a-a398-679125d8b510
-- title:
--   Eisenstein coefficients of a matched pseudo-Eisenstein series on the unitary axis
-- statement:
--   Throughout, $K$ is a number field, and $0 < \alpha < \beta$ are real. Write $P$ for the carrier data produced by `productionPinsOf` from the canonical truncation domain [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the level subgroups $M \mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke elements $v \mapsto$ `heckeGen (𝓞 K) K v` and the box `adelicBox K`; thus the measurable structure of $P$ is the Borel one on $\mathrm{GL}_2(\mathbb{A}_K)$, its measure is `adelicGLHaar (Fin 2) (𝓞 K) K`, its domain is the canonical truncation domain, its central subgroup is the full group $\mathbb{A}_K^\times$ of ideles, and its additive measure is `adelicAddHaar (𝓞 K) K` conditioned on `adelicBox K`.
--
--   The input data are: a set $\Phi_K$ of adelic matrices, on which no condition is imposed; reals $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$, $0 < d_{1K} < d_{2K}$ and a finite set $T_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ subject to the Siegel covering hypothesis `hcovK`, which says that the union of the right translates $(\cdot\, x)\,[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,]$ over $x \in T_K$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo global points and the centre, i.e. every $g$ admits $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g z$ in that union (the centre-cut Siegel set consisting of the $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c_K$, whose window quantities satisfy `xWindowSq` $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K}, d_{2K}]$); a Haar measure $\nu_{ZK}$ on the idele units together with a set $\Omega_K$ that is a fundamental domain for the subgroup of principal ideles, the image of $K^\times$; a finite set $S_K$ of finite places; a character $\xi_K$ of the full subgroup of the idele units with values in $\mathbb{C}^\times$, assumed continuous (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value one (`hξu`); an ideal $N$ of $\mathcal{O}_K$ such that every place dividing $N$ belongs to $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, i.e. a finite collection of row-isometry representation types at each infinite place.
--
--   Let $\alpha_m : \mathbb{A}_K^\times \to \mathbb{R}^\times$ be the unit-valued monoid homomorphism obtained from the distributive Haar character of $\mathbb{A}_K$ through $\mathbb{R}_{\ge 0} \to \mathbb{R}$, the adele ring carrying its Borel structure, and let $h_{\alpha m}$ be the hypothesis that $\alpha_m$ takes positive values. The assertion is the existence of a real $\kappa > 0$, depending only on the data above, such that for all further data as follows the two displayed identities hold.
--
--   The cuspidal basis data: a type $\iota$, functions $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ and $\mathrm{cls} : \iota \to$ `HeckeEigensystem K ℂ`, with (`hb`) each $\mathrm{cls}\,i$ lying in `cuspClasses K` $P\,\xi_K\,N\,S_K$ — that is, its level is $N$, its Hecke and central eigenvalues vanish at the places of $S_K$, and its isotypic cusp submodule is nonzero — and each $b\,i$ lying in the intersection of the isotypic cusp submodule of $\mathrm{cls}\,i$ with `archCutSubmodule K tysK`, the intersection over the infinite places of the sums of the prescribed type submodules; (`hbn`) $\int_{D} b_i \overline{b_i} = 1$ and (`hbo`) $\int_{D} b_i \overline{b_j} = 0$ for $i \ne j$, the integrals taken over the canonical truncation domain $D$ against `adelicGLHaar`; (`hbs`) for every class $\pi$ in `cuspClasses`, the fibre $\{i \mid \mathrm{cls}\,i = \pi\}$ is finite and the complex span of $b$ on it equals the isotypic cusp submodule of $\pi$ cut by the archimedean types; and (`hbc`) the completeness statement that any $\varphi$ which is a smooth cuspidal automorphic function for $P$ and $\xi_K$, continuous, right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, lying in `archCutSubmodule K tysK`, and orthogonal to every $b_i$ over $D$, vanishes almost everywhere for `adelicGLHaar` restricted to $D$.
--
--   The Eisenstein family data: a countable type $\iota_E$ and characters $\mu, \nu : \iota_E \to \mathrm{Hom}(\mathbb{A}_K^\times, \mathbb{C}^\times)$ with the hypotheses that each $\mu_e, \nu_e$ is unitary, is an idele class character (trivial on $K^\times$), is continuous, that $\mu_e \nu_e = \xi_K$, and that distinct indices are separated on the norm-one ideles (the kernel of the distributive Haar character). Next, integers $n_E(e)$ and sections $\varphi_E(e,j,s,\cdot)$ for $j \in \mathrm{Fin}(n_E(e))$, subject to the section hypotheses: $\varphi_E(e,j,s)$ is an induced section for the pair of Borel characters `etaFst (μ e) αm hαm s` $= \mu_e \alpha_m^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $= \nu_e \alpha_m^{-(s+1/2)}$, meaning $\varphi(bg) = \eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for upper triangular $b$; it is archimedean $\mathbf{K}$-finite and smooth for the finite-adelic subgroup; jointly continuous in $(s,g)$; entire in $s$ for fixed $g$; uniformly $\mathbf{K}$-finite at each infinite place through one finite-dimensional space $W$ of functions on the row-isometry subgroup; flat, i.e. $\varphi_E(e,j,s,k) = \varphi_E(e,j,0,k)$ for $k$ in the adelic maximal compact subgroup; right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; contained in `archCutSubmodule K tysK`; orthonormal over the maximal compact subgroup against `maximalCompactHaar K` at $s=0$; spanning, in the sense that for each $e$, each real $t$ and each section $\varphi_0$ induced at $s = it$ for $(\mu_e,\nu_e)$ which is continuous, archimedean $\mathbf{K}$-finite, level-$N$ invariant and of the prescribed archimedean types, $\varphi_0$ lies in the span of the $\varphi_E(e,j,it)$; and exhaustive (`_hpairs`): for any unitary continuous idele class characters $\mu', \nu'$ with $\mu'\nu' = \xi_K$, any real $t$ and any nonzero $\varphi_0$ with the same five properties at $s = it$, some $e$ satisfies $\mu_e = \mu'$ and $\nu_e = \nu'$ on the norm-one ideles. Finally sets $O_E(e,j) \subseteq \mathbb{C}$ and functions $E_E(e,j,s,\cdot)$, $N_E(e,j,s,\cdot)$ with the continuation hypothesis `_hEE` (nine clauses): $O_E(e,j)$ is open, preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ the functions $s \mapsto E_E(e,j,s,g)$ and $s \mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j) \times \mathrm{GL}_2(\mathbb{A}_K)$ jointly; for $\mathrm{Re}\,s > 1/2$, $E_E(e,j,s,g) = \varphi_E(e,j,s,g) + \sum_{\xi \in K} \varphi_E(e,j,s, w\, u(\xi)\, g)$ with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent matrix; and for $\mathrm{Re}\,s > 1/2$, $N_E(e,j,s,g) = \int_{\mathbb{A}_K} \varphi_E(e,j,s, w^{-1} u(x) g)\,dx$ against `adelicAddHaar (𝓞 K) K`.
--
--   The Paley–Wiener profile data: a finite type $\iota_P$ and characters $\mu_P, \nu_P : \iota_P \to \mathrm{Hom}(\mathbb{A}_K^\times, \mathbb{C}^\times)$, each unitary, an idele class character and continuous, with $\mu_P(e)(z)\nu_P(e)(z) = \xi_K(z)$ for all ideles $z$, together with an involutive swap $r_P : \iota_P \to \iota_P$ satisfying $\mu_P(r_P e) = \nu_P(e)$ and $\nu_P(r_P e) = \mu_P(e)$, and pairwise separation of distinct indices on the norm-one ideles. Sections $\psi_f(e,s,\cdot)$ are assumed to be induced for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`, jointly continuous, entire in $s$ for each $g$, and rapidly decreasing on vertical lines locally uniformly in $g$ (`_hψdec`): for each $e$, each $n \in \mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded above $m : \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^n \|\psi_f(e, \sigma' + it, g)\| \le m(t)$ whenever $|\sigma'| \le \sigma_0$, $t \in \mathbb{R}$, $g \in C$. No $\mathbf{K}$-finiteness is imposed on $\psi_f$. A function $\psi$ on $\mathrm{GL}_2(\mathbb{A}_K)$ is assumed to be a slab profile for the central subgroup of $P$ and $\xi_K$ (`_hψ`): measurable, invariant under left translation by unipotent matrices and by global Borel points, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1 > 0$, and with nonvanishing confined to a band of adelic heights; and (`_hψrep`) for every real $\sigma'$ and every $g$,
--   $$\psi(g) = \sum_{e \in \iota_P} (4\pi)^{-1} \int_{\mathbb{R}} \psi_f(e, \sigma' + it, g)\, dt.$$
--   The matching data are maps $\mathrm{em} : \iota_P \to \iota_E$ and $\tau : \iota_P \to \mathbb{R}$ with $\mu_P(i) = \mu_{\mathrm{em}(i)} \cdot$ `normPowChar K (τ i)` and $\nu_P(i) = \nu_{\mathrm{em}(i)} \cdot ($`normPowChar K (τ i)`$)^{-1}$, where `normPowChar K t` is the character $x \mapsto \|x\|^{it}$ of the ideles.
--
--   The conclusion has two conjuncts. First, for every $e \in \iota_E$ which is not of the form $\mathrm{em}(i)$, every $j \in \mathrm{Fin}(n_E(e))$ and every real $t$,
--   $$\int_{D} \;\mathrm{pseudoEisenstein}\,(\psi)(g)\, \overline{E_E(e, j, it, g)}\, d(\mathrm{adelicGLHaar}) = 0,$$
--   where $D$ is the canonical truncation domain and the pseudo-Eisenstein series is $\psi(g) + \sum_{\beta \in K} \psi(w\,u(\beta)\,g)$.
--
--   Second, for every $i \in \iota_P$, every $j \in \mathrm{Fin}(n_E(\mathrm{em}(i)))$ and every real $t$, setting $\mathrm{vol} \in \mathbb{C}$ to be the real measure `adelicAddHaar (𝓞 K) K` of `adelicBox K` and $t_E = i(t + \tau_i)$,
--   $$\int_{D} \mathrm{pseudoEisenstein}\,(\psi)(g)\, \overline{E_E(\mathrm{em}(i), j, t_E, g)}\, d(\mathrm{adelicGLHaar})$$
--   equals $\kappa$ times the sum of
--   $$\int \psi_f(i, it, k)\, \overline{\varphi_E(\mathrm{em}(i), j, t_E, k)}\, d(\mathrm{maximalCompactHaar}\,K)$$
--   and
--   $$\int \psi_f(r_P i, -it, k)\, \overline{\mathrm{vol}^{-1} N_E(\mathrm{em}(i), j, t_E, k)}\, d(\mathrm{maximalCompactHaar}\,K),$$
--   both integrals being over the adelic maximal compact subgroup. Thus the Paley–Wiener side is evaluated at the spectral parameter $it$ and at its reflection $-it$ through the swap $r_P$, while the Eisenstein side is evaluated at the shifted parameter $i(t + \tau_i)$, the second term carrying the Weyl intertwining datum $N_E$ normalised by the box volume.
--
--   This is the bridge identifying the coefficients of a pseudo-Eisenstein series against the axis continuations of the Eisenstein family with the values of the Paley–Wiener section data on the unitary axis, in the asymmetric two-term form in which the intertwining operator appears only on the Eisenstein side. It supplies the continuous-spectrum block in the spectral expansion over the canonical truncation domain, and is used by the results that combine the cuspidal projection, the residual projection and the continuous part into the full expansion of the truncated kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
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
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹),
    (∀ (e : ιE), (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ),
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0) ∧
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
    let vol : ℂ := (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)
    let tE : ℂ := (((t + τ i : ℝ) : ℂ)) * Complex.I
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K ψ g * conj (EE (em i) j tE g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (κ : ℂ) *
        ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K)) +
          ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (vol⁻¹ * NE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
