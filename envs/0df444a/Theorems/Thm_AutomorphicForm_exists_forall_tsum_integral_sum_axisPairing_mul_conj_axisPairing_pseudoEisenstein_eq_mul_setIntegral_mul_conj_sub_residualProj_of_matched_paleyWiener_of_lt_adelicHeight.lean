-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight
-- name    : AutomorphicForm.exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/6a8fffae-f79b-5154-9901-af0a2c89a603
-- title:
--   Polarised Paley–Wiener identity for axis pairings against a matched packet
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal O_K$, and $\alpha,\beta$ are reals with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`); $\Phi_0$ denotes [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the set of adelic matrices extracted (as the last component of `canonicalTruncationData`) from a truncation datum for the pair $(\alpha,\beta)$, and all integrals over $\Phi_0$ are taken with respect to the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $GL_2(\mathbb A_K)$.
--
--   **Frame data.** A set `ΦK` of adelic matrices is given, on which no hypothesis is imposed. *Siegel covering*: reals `cK uK d₁K d₂K` with `hcK : 0 < cK`, `hd₁K : 0 < d₁K`, `hdK : d₁K < d₂K`, a finite set `TK` of adelic matrices, and `hcovK`, which asserts `CoversModCentre K` for the union over $x\in$ `TK` of the right translates by $x$ of `centreCutSiegelSet K cK uK d₁K d₂K` (the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose local heights at all infinite places are $\ge c_K$, whose window squares are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$); that is, every $g\in GL_2(\mathbb A_K)$ can be moved into that union by left multiplication by a global point $\gamma\in GL_2(K)$ and right multiplication by a central idele. *Idele class measure*: a measurable and Borel structure on the idele group $\mathbb A_K^\times$, a Haar measure `νZK`, and a set `ΩK` which by `hΩK` is a fundamental domain for the range of $K^\times$ in $\mathbb A_K^\times$ with respect to `νZK`. *Character and level*: a finite set `SK` of finite places, a homomorphism `ξK` from the full subgroup $\top\le\mathbb A_K^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and of absolute value $1$ (`hξu`), an ideal `N` of $\mathcal O_K$ such that every prime dividing $N$ lies in `SK` (`hN`), and an archimedean type family `tysK`, consisting of a cardinality function on infinite places together with, at each place $w$, that many finite-dimensional representations of the row-isometry group of $K_w$. The module character $\alpha_m$ is the $\mathbb R^\times$-valued homomorphism obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` through $\mathbb R_{\ge 0}\to\mathbb R$, and `hαm` asserts that its values are positive.
--
--   The pins used throughout are `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: Borel structure and Haar measure on $GL_2(\mathbb A_K)$, domain $\Phi_0$, central subgroup $\top$, level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators `heckeGen (𝓞 K) K v`, and on the adele ring the Borel structure together with the additive Haar measure conditioned on `adelicBox K`.
--
--   **Assertion.** Under these hypotheses there exists a real $C>0$ such that for all further data as follows the three conclusions below hold.
--
--   *Cuspidal orthonormal frame*: a type `ι`, functions `b : ι → AdelicGL2 (𝓞 K) K → ℂ` and a labelling `cls : ι → HeckeEigensystem K ℂ` (a Hecke eigensystem being a nonzero level ideal together with families $a_v,b_v$ of complex eigenvalues), subject to: `hb`, each `cls i` lies in `cuspClasses` for the above pins, `ξK`, `N`, `SK` (i.e. has level $N$, has $a_v=b_v=0$ for $v\in S_K$, and has nonzero isotypic cuspidal submodule) and `b i` lies in the isotypic cuspidal submodule of `cls i` intersected with `archCutSubmodule K tysK` (the intersection over infinite places $w$ of the sum of the type submodules attached to the representations `tysK.rep w i`); `hbn`, each `b i` has $\int_{\Phi_0} b_i\overline{b_i}=1$; `hbo`, $\int_{\Phi_0} b_i\overline{b_j}=0$ for $i\ne j$; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb C$-span of the corresponding $b_i$ is the isotypic cuspidal submodule of $\pi$ intersected with `archCutSubmodule K tysK`; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function at the pins for `ξK` (namely in the space `LsXiMember` attached to the pins together with the cuspidality condition `IsCuspidalFn` for unipotent matrices and the conditioned adelic measure, and `IsKfSmooth`), continuous, invariant under right translation by the level group $U(N)$, of the prescribed archimedean types, and orthogonal on $\Phi_0$ to every $b_i$, vanishes almost everywhere on $\Phi_0$.
--
--   *Eisenstein packet*: a countable type `ιE`, families $\mu,\nu:\iota_E\to \operatorname{Hom}(\mathbb A_K^\times,\mathbb C^\times)$ with hypotheses `_hμ`, `_hν` (unitary), `_hμic`, `_hνic` (trivial on $K^\times$), `_hμc`, `_hνc` (continuous), `_hμν` ($\mu_e\nu_e=\xi_K$ pointwise) and `_hdist` (distinct indices are separated on the norm-one ideles, the kernel of `distribHaarChar`); integers `nE e` and sections `φE e j s` with: `_hφE`, each $\varphi_{e,j,s}$ is an induced section for the pair `etaFst (μ e) αm hαm s` $=\mu_e\cdot|\cdot|^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\cdot|\cdot|^{-(s+1/2)}$, i.e. $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK` archimedean $K$-finiteness; `_hφEf` smoothness under the finite part; `_hφEjc` joint continuity in $(s,g)$; `_hφEhol` holomorphy in $s$; `_hφEKu` existence, at each infinite place, of a finite-dimensional space of functions on the row-isometry subgroup containing all right translates; `_hφEflat` flatness, $\varphi_{e,j,s}=\varphi_{e,j,0}$ on `adelicMaximalCompact K`; `_hφElev` invariance under $U(N)$; `_hφEty` membership in `archCutSubmodule K tysK`; `_hφEon` orthonormality of the $\varphi_{e,j,0}$ over the maximal compact subgroup with respect to `maximalCompactHaar K`; `_hφEspan`, for each $e$ and each real $t$ every such section on the line $s=it$ with the same invariance and types lies in the span of the $\varphi_{e,j,it}$; and `_hpairs`, every unitary, idele-class, continuous pair $(\mu',\nu')$ with $\mu'\nu'=\xi_K$ admitting a nonzero such section on a line $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. *Continuations*: sets `OE e j ⊆ ℂ` and families `EE e j s`, `NE e j s`, subject to `_hEE` (nine clauses): `OE e j` is open and preconnected, contains the imaginary axis and the half plane $\operatorname{Re}s>1/2$, the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of `OE e j` for each $g$, both are continuous on `OE e j` $\times$ `univ` jointly in $(s,g)$, and for $\operatorname{Re}s>1/2$ one has $E_{e,j}(s)(g)=\varphi_{e,j,s}(g)+\sum'_{\xi\in K}\varphi_{e,j,s}(w\,u(\xi)g)$ with $w=$ `adelicWeyl` and $u$ the unipotent embedding, and $N_{e,j}(s)(g)=$ `weylIntertwiningIntegral` of $\varphi_{e,j,s}$ at $g$ for the additive adelic Haar measure.
--
--   *Test packet*: a finite type `ιP`, families $\mu_P,\nu_P$ with `_hμ`, `_hν` unitary, `_hμic`, `_hνic` idele class, `_hμc`, `_hνc` continuous, `_hμν` the product $\mu_P(z)\nu_P(z)=\xi_K(z)$ for $z$ in the central subgroup of the pins, a map `rP` with `_hr` interchanging $\mu_P$ and $\nu_P$, and `_hdist` separation on the norm-one ideles; sections `ψf e s` with `_hψf` the induced-section property for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`, `_hψjc` joint continuity, `_hψhol` holomorphy in $s$, `_hψK` archimedean $K$-finiteness, `_hψsm` smoothness under the finite part, `_hψKu` the finite-dimensional archimedean translate condition, and `_hψdec` the Paley–Wiener decay: for every $e$, every $n\in\mathbb N$, every $\sigma_0$ and every compact $C$ there is an integrable, bounded above $m:\mathbb R\to\mathbb R$ with $(1+|t|)^n\|\psi_e(\sigma'+it)(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. A function `ψ` is given with `_hψ` the slab-profile conditions `IsSlabProfile` (measurability, invariance under left multiplication by unipotent matrices and by global Borel points, $\xi_K$-equivariance under the centre, boundedness on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and vanishing outside a band $[a,b]$, $a>0$, of adelic heights) and `_hψrep`, that for every real $\sigma'$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb R}\psi_e(\sigma'+it)(g)\,dt$. A matching `em : ιP → ιE` and reals `τ` are given with `_hem`: $\mu_P(i)=\mu(\mathrm{em}\,i)\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P(i)=\nu(\mathrm{em}\,i)\cdot\|\cdot\|^{-i\tau_i}$ in terms of `normPowChar`; further `_hψlev` invariance of each $\psi_e(s)$ under $U(N)$ and `_hψty` membership in `archCutSubmodule K tysK`.
--
--   *Residual projection and test vector*: a function `pψ` with `_hpψ` automorphic at the pins for `ξK`, `_hpψc` that for every $\varepsilon>0$ there is an automorphic $r$ in [`AutomorphicForm.residualSpan`](def/AutomorphicForm_ResidualSpan.html#L12) (the span of the functions $\chi\circ\det$ for characters $\chi$ with $\chi^2=\xi_K$ on the central subgroup) with $\|p_\psi-r\|_{L^2(\Phi_0)}<\varepsilon$, and `_hpψo` that $\int_{\Phi_0}(\theta_\psi-p_\psi)\overline h=0$ for every automorphic $h$ in the residual span, where $\theta_\psi=$ [`AutomorphicForm.pseudoEisenstein K ψ`](def/AutomorphicForm_SlabProfile.html#L32), $\theta_\psi(g)=\psi(g)+\sum'_{\beta\in K}\psi(w\,u(\beta)g)$. Finally a function `u` with `_hu` automorphic at the pins for `ξK`, and `_hub`: there is a real $T$ with $u(g)=0$ for every $g\in\Phi_0$ of adelic height greater than $T$.
--
--   **Conclusions.** Writing $\Theta_v(e,j,s)=\int_{\Phi_0}v(g)\overline{E_{e,j}(s)(g)}\,dg$:
--
--   (i) for every $e\in\iota_E$ and $j<n_E(e)$ the function $t\mapsto \Theta_u(e,j,it)\,\overline{\Theta_{\theta_\psi}(e,j,it)}$ is integrable on $\mathbb R$;
--
--   (ii) the function $e\mapsto \int_{\mathbb R}\sum_{j<n_E(e)}\Theta_u(e,j,it)\,\overline{\Theta_{\theta_\psi}(e,j,it)}\,dt$ is summable over $\iota_E$;
--
--   (iii) $\displaystyle\sum_{e\in\iota_E}\int_{\mathbb R}\sum_{j<n_E(e)}\Theta_u(e,j,it)\,\overline{\Theta_{\theta_\psi}(e,j,it)}\,dt \;=\; C\int_{\Phi_0}u(g)\,\overline{\theta_\psi(g)-p_\psi(g)}\,dg,$ with $C$ the constant produced above, viewed in $\mathbb C$; in particular $C$ depends only on the frame data and not on any of the subsequent families.
--
--   This is the continuous-spectrum block of the spectral expansion on the truncation domain, in polarised form: it identifies the pairing of an arbitrary height-capped automorphic test vector against the pseudo-Eisenstein series of a Paley–Wiener slab profile with the integral over the unitary axis of the corresponding Eisenstein coefficients, up to a frame constant and after removal of the residual part. It is used in the estimate [`AutomorphicForm.exists_forall_tsum_integral_sum_normSq_setIntegral_axis_continuation_sub_le_mul_sq_of_forall_norm_setIntegral_sub_mul_conj_le`](thm.html#AutomorphicForm.exists_forall_tsum_integral_sum_normSq_setIntegral_axis_continuation_sub_le_mul_sq_of_forall_norm_setIntegral_sub_mul_conj_le), and is applied with the test vector taken to be a pseudo-Eisenstein series of another packet or a truncated theta-type vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight.lean

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

theorem AutomorphicForm.exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight
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
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0),
    (∀ (e : ιE) (j : Fin (nE e)), Integrable (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ∧
    ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (C : ℂ) * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        u g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
