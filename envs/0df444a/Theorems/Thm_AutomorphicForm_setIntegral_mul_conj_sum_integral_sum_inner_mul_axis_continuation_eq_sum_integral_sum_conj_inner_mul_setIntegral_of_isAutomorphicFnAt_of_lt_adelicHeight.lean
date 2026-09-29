-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
-- name    : AutomorphicForm.setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a5de81a8-515e-5ed2-9ad9-36f8cc492b57
-- title:
--   Term-by-term pairing of truncated automorphic function with Eisenstein packet
-- statement:
--   Throughout, $K$ is a number field, and $\alpha<\beta$ are reals with $0<\alpha$. Write $D=\mathtt{canonicalTruncationDomain }K\ \alpha\ \beta$ for the canonical truncation domain of the slab $(\alpha,\beta)$, $\mu_{\mathrm{GL}}=\mathtt{adelicGLHaar (Fin 2)}$ for Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, and
--   $$\mathrm{pins}=\mathtt{productionPinsOf } K\ D\ (M\mapsto \mathtt{principalLevel } M\sqcap\mathtt{finiteAdelicGL2Subgroup})\ (v\mapsto\mathtt{heckeGen } v)\ (\mathtt{adelicBox } K)$$
--   for the carrier data with Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, domain $D$, central subgroup $\top\le\mathbb{A}_K^\times$, level subgroups $U(M)=\mathtt{principalLevel}(M)\sqcap\mathtt{finiteAdelicGL2Subgroup}$, Hecke generators $\mathtt{heckeGen } v$, and additive measure the conditioning of $\mathtt{adelicAddHaar}$ on $\mathtt{adelicBox } K$.
--
--   *Geometric and measure-theoretic data.* A set $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ such that the union of the right translates $(\cdot\, x)''\,\mathtt{centreCutSiegelSet } K\ c_K\ u_K\ d_{1K}\ d_{2K}$ over $x\in T_K$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre in the sense of `CoversModCentre` (every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central idele $z$ with $\gamma g z$ in the set); a Borel measurable structure on $\mathbb{A}_K^\times$, a Haar measure $\nu_{ZK}$ on it, and a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{ZK}$.
--
--   *Central character, level and types.* A finite set $S_K$ of finite places of $K$; a character $\xi_K$ on the whole group $\mathbb{A}_K^\times$ (as a homomorphism from $\top$ to $\mathbb{C}^\times$) which is continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary, $\lVert\xi_K(z)\rVert=1$ for all $z$ (`hξu`); an ideal $N\subseteq\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, whose associated cut submodule $\mathtt{archCutSubmodule } K\ \mathrm{tys}_K$ is the intersection over infinite places $w$ of the sums of the type submodules of the chosen representations at $w$.
--
--   For $\alpha_m$ the monoid homomorphism $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ via $\mathbb{R}_{\ge0}\to\mathbb{R}$, and for a hypothesis $h_{\alpha m}$ that $\alpha_m$ takes strictly positive values, the assertion is universally quantified over the following further data.
--
--   *Cuspidal orthonormal family.* A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}_i\in\mathtt{HeckeEigensystem } K\ \mathbb{C}$ subject to: `hb`, each $\mathrm{cls}_i$ lies in $\mathtt{cuspClasses}$ for $\mathrm{pins},\xi_K,N,S_K$ (level $N$, vanishing $a_v=b_v=0$ at all $v\in S_K$, non-zero isotypic cusp submodule) and $b_i$ lies in the corresponding isotypic cusp submodule intersected with the archimedean cut submodule; `hbn`, $\int_D b_i\overline{b_i}\,d\mu_{\mathrm{GL}}=1$; `hbo`, $\int_D b_i\overline{b_j}\,d\mu_{\mathrm{GL}}=0$ for $i\neq j$; `hbs`, for each class $\pi$ the fibre $\{i:\mathrm{cls}_i=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ is the $\pi$-isotypic cusp submodule intersected with the archimedean cut submodule; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function at $\mathrm{pins}$ with character $\xi_K$, continuous, right invariant under $U(N)$, lying in the archimedean cut submodule and orthogonal over $D$ to every $b_i$, vanishes almost everywhere for $\mu_{\mathrm{GL}}$ restricted to $D$.
--
--   *Continuous-spectrum frame.* A countable type $\iota_E$, families of characters $\mu_e,\nu_e$ of $\mathbb{A}_K^\times$, integers $n_E(e)$ and sections $\varphi_{E}(e,j,s):\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, subject to the hypothesis groups: unitarity and idele-class triviality of $\mu_e$ and $\nu_e$, continuity of both, the product relation $\mu_e\nu_e=\xi_K$, and separation of distinct indices on the norm-one ideles (the kernel of the distributive Haar character); and, for the sections, membership in the induced model $\mathtt{IsInducedSection}$ for the pair $\big(\mu_e\cdot\alpha_m^{\,s+1/2},\ \nu_e\cdot\alpha_m^{-(s+1/2)}\big)$ (that is, $\varphi(bg)$ equals the product of the two characters evaluated at the diagonal entries of the upper-triangular $b$ times $\varphi(g)$), archimedean $\mathbf{K}$-finiteness, smoothness for the finite-adelic subgroup, joint continuity in $(s,g)$, holomorphy in $s$, a uniform finite-dimensionality of the right translates along $\mathtt{archRowIsometrySubgroup } K\ w$ at each infinite place, flatness on the adelic maximal compact ($\varphi_E(e,j,s)$ agrees with $\varphi_E(e,j,0)$ there), right invariance under $U(N)$, membership in the archimedean cut submodule, orthonormality of $\varphi_E(e,i,0),\varphi_E(e,j,0)$ against $\mathtt{maximalCompactHaar } K$, spanning of all such sections at $s=it$ by the finitely many $\varphi_E(e,j,it)$, and exhaustiveness `_hpairs`: every unitary continuous idele-class pair $(\mu',\nu')$ with $\mu'\nu'=\xi_K$ admitting a non-zero section of the stated kind at some $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   *Axis continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E(e,j,s)$, $N_E(e,j,s)$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ such that (`_hEE`) each $O_E(e,j)$ is open, preconnected and contains both the imaginary axis $\{\operatorname{Re} s=0\}$ and the half-plane $\{\operatorname{Re} s>1/2\}$; for each $g$ both $s\mapsto E_E(e,j,s)(g)$ and $s\mapsto N_E(e,j,s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$ jointly; for $\operatorname{Re} s>1/2$, $E_E(e,j,s)(g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}\varphi_E(e,j,s)\big(w\,n(\xi)\,g\big)$ with $w=\mathtt{adelicWeyl}$ and $n(\xi)$ the unipotent matrix of the image of $\xi$; and $N_E(e,j,s)(g)$ is the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi_E(e,j,s)(w^{-1}n(x)g)\,dx$ for $\mathtt{adelicAddHaar}$.
--
--   *Paley–Wiener datum.* A finite type $\iota_P$, characters $\mu_{P,i},\nu_{P,i}$ which are unitary, idele-class trivial and continuous, satisfy $\mu_{P,i}(z)\nu_{P,i}(z)=\xi_K(z)$ for central $z$, are separated on the norm-one ideles for distinct indices, and carry a swap $r_P:\iota_P\to\iota_P$ with $\mu_{P,r_P(i)}=\nu_{P,i}$ and $\nu_{P,r_P(i)}=\mu_{P,i}$; sections $\psi_f(i,s)$ which are induced sections for $\big(\mu_{P,i}\cdot\alpha_m^{\,s+1/2},\ \nu_{P,i}\cdot\alpha_m^{-(s+1/2)}\big)$, jointly continuous, holomorphic in $s$, archimedean $\mathbf{K}$-finite, smooth for the finite-adelic subgroup, uniformly $\mathbf{K}$-finite at each infinite place, right invariant under $U(N)$ and in the archimedean cut submodule, and satisfy the vertical-strip decay `_hψdec`: for each $i$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\lVert\psi_f(i,\sigma'+it)(g)\rVert\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Further, a function $\psi$ which is a slab profile for $\top$ and $\xi_K$ (measurable; invariant under left translation by unipotents and by rational Borel elements; transforming by $\xi_K$ under the centre; bounded on each determinant-norm slab; and supported in a band of adelic heights), with the contour representation `_hψrep`: $\psi(g)=\sum_{i}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(i,\sigma'+it)(g)\,dt$ for every $\sigma'$ and $g$. Finally a matching $e:\iota_P\to\iota_E$ and shifts $\tau:\iota_P\to\mathbb{R}$ with $\mu_{P,i}=\mu_{e(i)}\cdot\lVert\cdot\rVert^{i\tau_i}$ and $\nu_{P,i}=\nu_{e(i)}\cdot\lVert\cdot\rVert^{-i\tau_i}$, where $\lVert\cdot\rVert^{i t}=\mathtt{normPowChar } K\ t$.
--
--   *The test vector.* A function $u:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying the predicate $\mathtt{IsAutomorphicFnAt } K\ \mathrm{pins}\ \xi_K$, that is `LsXiMember` for the Borel structure and Haar measure of $\mathrm{pins}$, the domain $D$, the central subgroup $\top$ and the character $\xi_K$, together with the height cap `_hub`: there is $T\in\mathbb{R}$ with $u(g)=0$ for every $g\in D$ whose adelic height exceeds $T$.
--
--   Write, for $i\in\iota_P$, $j\in\mathrm{Fin}(n_E(e(i)))$ and $t\in\mathbb{R}$,
--   $$c_{i,j}(t)=\int_{\mathtt{adelicMaximalCompact } K}\psi_f(i,it)(k)\,\overline{\varphi_E\big(e(i),j,i(t+\tau_i)\big)(k)}\,d(\mathtt{maximalCompactHaar } K),$$
--   $$\Theta_{i,j}(t)=\int_{D}u(g)\,\overline{E_E\big(e(i),j,i(t+\tau_i)\big)(g)}\,d\mu_{\mathrm{GL}}.$$
--
--   The conclusion is the conjunction of two statements. First, for every $i\in\iota_P$ and every $j\in\mathrm{Fin}(n_E(e(i)))$ the function $t\mapsto \overline{c_{i,j}(t)}\,\Theta_{i,j}(t)$ is integrable on $\mathbb{R}$. Second,
--   $$\int_{D}u(g)\,\overline{\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j}c_{i,j}(t)\,E_E\big(e(i),j,i(t+\tau_i)\big)(g)\,dt}\;d\mu_{\mathrm{GL}}\;=\;\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j}\overline{c_{i,j}(t)}\,\Theta_{i,j}(t)\,dt,$$
--   the integrals over $D$ being taken against $\mu_{\mathrm{GL}}$.
--
--   This is the Fubini interchange step for the continuous spectrum: it evaluates the inner product over the truncated domain of a height-capped automorphic function against an Eisenstein wave packet built from a Paley–Wiener datum term by term in the packet's parameters, without assuming the wave-packet representation itself. It is used in the polarised identification of pseudo-Eisenstein pairings with wave-packet pairings and in the attendant Plancherel-type bound and orthogonality statements for the truncated spectral decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight.lean

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

theorem AutomorphicForm.setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
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
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0),
    (∀ (i : ιP) (j : Fin (nE (em i))), Integrable (fun t : ℝ =>
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        u g * conj (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              u g * conj (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
