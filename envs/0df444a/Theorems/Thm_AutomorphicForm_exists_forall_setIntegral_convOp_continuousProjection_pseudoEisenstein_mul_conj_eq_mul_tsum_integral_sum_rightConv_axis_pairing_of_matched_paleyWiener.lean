-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_convOp_continuousProjection_pseudoEisenstein_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_pseudoEisenstein_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/c4a8fd87-5c2c-5e50-9721-18cb6653d25f
-- title:
--   Paley–Wiener spectral form of R(f) on the continuous spectrum
-- statement:
--   Throughout, $K$ is a number field with adele ring $\mathbb{A}=\mathbb{A}_K$, and $G=\mathrm{GL}_2(\mathbb{A})$ is `AdelicGL2 (𝓞 K) K`. Write $\mu_G$ for the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` attached to the Borel $\sigma$-algebra on $G$, $\Phi_0$ for the truncation domain [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) (the third component of the canonical choice of truncation datum for the parameters $\alpha,\beta$), and $P$ for the carrier pins `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, i.e. the package consisting of the Borel $\sigma$-algebra on $G$ with $\mu_G$, the domain $\Phi_0$, the central subgroup $Z=\top$ of $\mathbb{A}^\times$, the level groups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen`, and on the adeles the Borel $\sigma$-algebra together with the additive Haar measure conditioned on the box `adelicBox K`. Also $\mathbf{K}$ denotes `adelicMaximalCompact K` (finite part in the integral matrices, archimedean components row isometries) with its Haar measure `maximalCompactHaar K`.
--
--   The ambient data are: reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K\subseteq G$, on which no condition is imposed and which occurs nowhere else in the statement; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, and a finite set $T_K\subseteq G$ such that the union $\bigcup_{x\in T_K}(\cdot\,x)$-translates of `centreCutSiegelSet K cK uK d₁K d₂K` (matrices with integral finite part, archimedean local heights at least $c_K$, window squares at most $u_K^2$, and archimedean determinant norms in $[d_{1K},d_{2K}]$) covers $G$ modulo $\mathrm{GL}_2(K)$ on the left and the centre on the right, in the sense of `CoversModCentre`; a Haar measure $\nu_{ZK}$ on $\mathbb{A}^\times$ for a Borel measurable structure on it, together with a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_{ZK}$; a finite set $S_K$ of finite places of $K$; a character $\xi_K$ of the full subgroup $\top$ of $\mathbb{A}^\times$ with values in $\mathbb{C}^\times$, assumed continuous (`hξc`), trivial on the principal ideles (`hξt`) and unitary (`hξu`); an ideal $N\subseteq\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$ (a number of types at each infinite place together with the types themselves), whose associated submodule of functions on $G$ is `archCutSubmodule K tysK`, the intersection over the infinite places of the sums of the corresponding archimedean type components.
--
--   The character $\alpha_m:\mathbb{A}^\times\to\mathbb{R}^\times$ is the monoid homomorphism obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 K) K)` by composing with the coercion $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passing to units, and $h_{\alpha m}$ asserts that all its values are positive; for a character $\chi$ of $\mathbb{A}^\times$ and $s\in\mathbb{C}$, `etaFst χ αm hαm s` $=\chi\cdot\alpha_m^{\,s+1/2}$ and `etaSnd χ αm hαm s` $=\chi\cdot\alpha_m^{-(s+1/2)}$.
--
--   The assertion is the existence of a real $\kappa>0$ — depending only on the data listed above, hence uniform in everything introduced below — such that the following holds for all the remaining data.
--
--   *(i) Cuspidal orthonormal system.* A type $\iota$, functions $b_i:G\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}_i$ (each a level ideal $\neq\bot$ together with families $a_v,b_v$ of complex numbers indexed by the finite places), subject to: `hb`, that each $\mathrm{cls}_i$ lies in `cuspClasses K P ξK N SK` (level $N$, vanishing of $a_v$ and $b_v$ for $v\in S_K$, and non-trivial isotypic cuspidal submodule) and each $b_i$ lies in `isotypicCuspSubmodule K P ξK N SK (cls i) ⊓ archCutSubmodule K tysK`, the isotypic submodule being the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these data; `hbn` and `hbo`, that $\int_{\Phi_0}b_i\overline{b_i}\,d\mu_G=1$ and $\int_{\Phi_0}b_i\overline{b_j}\,d\mu_G=0$ for $i\neq j$; `hbs`, that for every $\pi\in$ `cuspClasses K P ξK N SK` the fibre $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the span of the corresponding $b_i$ is exactly the $\pi$-isotypic cuspidal submodule intersected with `archCutSubmodule K tysK`; and `hbc`, completeness: any $\varphi:G\to\mathbb{C}$ which satisfies `IsSmoothCuspAutomorphicFnAt K P ξK` (automorphic in the sense of `IsAutomorphicFnAt` for $P$ and $\xi_K$, cuspidal in the sense of `IsCuspidalFn` for the conditioned adelic measure and the unipotent embedding, and a smooth vector for the finite-adelic subgroup), is continuous, is invariant under right translation by $P.U\,N=$ `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, lies in `archCutSubmodule K tysK`, and is orthogonal to every $b_i$ over $\Phi_0$, vanishes $\mu_G$-almost everywhere on $\Phi_0$.
--
--   *(ii) Continuous-spectrum families.* A countable type $\iota_E$ and characters $\mu_e,\nu_e$ of $\mathbb{A}^\times$, assumed unitary, trivial on principal ideles, continuous, with $\mu_e\nu_e=\xi_K$, and pairwise separated on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16); integers $n_E(e)$ and families $\varphi_{e,j}(s)\in$ functions on $G$ satisfying: each $\varphi_{e,j}(s)$ is a section induced from $(\mathrm{etaFst}(\mu_e,s),\mathrm{etaSnd}(\nu_e,s))$, i.e. $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; archimedean $K$-finiteness and $K_f$-smoothness; joint continuity in $(s,g)$; holomorphy in $s$ for fixed $g$; uniform archimedean $K$-finiteness at each infinite place (a single finite-dimensional space containing all right-translate functions on `archRowIsometrySubgroup K w`); flatness, $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ for $k\in\mathbf{K}$; invariance under right translation by `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; membership in `archCutSubmodule K tysK`; orthonormality over $\mathbf{K}$ at $s=0$, $\int_{\mathbf{K}}\varphi_{e,i}(0)\overline{\varphi_{e,j}(0)}=\delta_{ij}$; spanning (`_hφEspan`), that every non-specified section $\varphi_0$ induced from $(\mathrm{etaFst}(\mu_e,it),\mathrm{etaSnd}(\nu_e,it))$ which is continuous, archimedean $K$-finite, level-$N$ right invariant and of the given archimedean types lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it)$; and exhaustiveness (`_hpairs`), that for any pair $(\mu',\nu')$ of continuous unitary characters trivial on principal ideles with $\mu'\nu'=\xi_K$ and any non-zero section $\varphi_0$ at $s=it$ with the same regularity, level and type conditions, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   *(iii) Analytic continuations.* Sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j}(s),N_{e,j}(s)$ of functions on $G$ such that (`_hEE`) each $O_{e,j}$ is open, preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times G$; and for $\mathrm{Re}\,s>1/2$ one has the Bruhat expansions $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}\varphi_{e,j}(s)(w\,u(\xi)g)$ with $w=$ `adelicWeyl` and $u(\cdot)$ the unipotent embedding, and $N_{e,j}(s)(g)=\int_{\mathbb{A}}\varphi_{e,j}(s)(w^{-1}u(x)g)\,dx$, the Weyl intertwining integral against the adelic additive Haar measure.
--
--   *(iv) Test function.* A continuous compactly supported $f:G\to\mathbb{C}$ which is factorizable (`IsFactorizableTestFn`: a product of an archimedean factor given by a smooth compactly supported function of the archimedean entries and a finite test factor), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for $\mathrm{tys}_K$ (`IsArchBiFinite`: $g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tysK` and $f$ in the dual cut submodule).
--
--   *(v) Paley–Wiener profile data.* A finite type $\iota_P$, characters $\mu_{P,e},\nu_{P,e}$ of $\mathbb{A}^\times$ which are unitary, trivial on principal ideles and continuous, with $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for $z$ in $P.Z$, pairwise separated on the norm-one ideles, and a map $r_P:\iota_P\to\iota_P$ interchanging the two characters, $\mu_{P,r_P e}=\nu_{P,e}$ and $\nu_{P,r_P e}=\mu_{P,e}$; families $\varphi_{f,e}(s),\psi_{f,e}(s)$ of sections induced from $(\mathrm{etaFst}(\mu_{P,e},s),\mathrm{etaSnd}(\nu_{P,e},s))$, jointly continuous in $(s,g)$ and holomorphic in $s$ for fixed $g$, the $\psi$-family moreover archimedean $K$-finite, $K_f$-smooth and uniformly $K$-finite at each infinite place; vertical decay hypotheses `_hφdec` and `_hψdec`, requiring for every $e$, every $n\in\mathbb{N}$, every $\sigma_0$ and every compact $C\subseteq G$ an integrable bounded majorant $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\varphi_{f,e}(\sigma'+it)(g)\|\le m(t)$ (respectively for $\psi_{f,e}$) for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$, $g\in C$; and two functions $\varphi,\psi:G\to\mathbb{C}$ which are slab profiles for $\xi_K$ in the sense of `IsSlabProfile` (measurable, invariant under left translation by unipotents and by global Borel elements, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab, and supported in a height band), represented on every vertical line by $\varphi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\varphi_{f,e}(\sigma'+it)(g)\,dt$ and $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_{f,e}(\sigma'+it)(g)\,dt$ for every $\sigma'\in\mathbb{R}$ and $g\in G$.
--
--   *(vi) Matching.* Maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu_{P,i}=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau(i)}$ and $\nu_{P,i}=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau(i)}$, the twists being [`NumberField.TateGlobal.normPowChar K (τ i)`](def/NumberField_NormPowChar.html#L22) and its inverse.
--
--   *(vii) Three-way decompositions.* Functions $u_{c,1},u_{r,1},u_{e,1}$ and $u_{c,2},u_{r,2},u_{e,2}$ on $G$, all satisfying `IsAutomorphicFnAt K P ξK`, such that for each index: the first has almost everywhere vanishing constant term $g\mapsto\int u_c(u(x)g)\,d\nu(x)$ for the conditioned adelic measure $P.\nu$; the second is approximable in $L^2(\mu_G|_{\Phi_0})$, to within any $\varepsilon>0$, by automorphic elements of [`AutomorphicForm.residualSpan (𝓞 K) K P.Z ξK`](def/AutomorphicForm_ResidualSpan.html#L12), the span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ of $\mathbb{A}^\times$ with $\chi^2=\xi_K$ on $P.Z$; the third is orthogonal over $\Phi_0$ to every automorphic $h$ which either has almost everywhere vanishing constant term or lies in the residual span; and, finally, `_hsum₁` and `_hsum₂`, that $\mathrm{pseudoEisenstein}(\varphi)=u_{c,1}+u_{r,1}+u_{e,1}$ and $\mathrm{pseudoEisenstein}(\psi)=u_{c,2}+u_{r,2}+u_{e,2}$ almost everywhere for $\mu_G$ restricted to $\Phi_0$, where $\mathrm{pseudoEisenstein}(\phi)(g)=\phi(g)+\sum_{\beta\in K}\phi(w\,u(\beta)g)$.
--
--   Under all of this the conclusion is the single identity
--   $$\int_{\Phi_0}\bigl(\mathrm{convOp}(f)u_{e,2}\bigr)(g)\,\overline{u_{e,1}(g)}\,d\mu_G(g)=\kappa\sum_{e\in\iota_E}\int_{\mathbb{R}}\sum_{i=1}^{n_E(e)}\sum_{j=1}^{n_E(e)}a_{e,ij}(t)\,\Bigl(\Theta_\psi(e,j,t)\,\overline{\Theta_\varphi(e,i,t)}\Bigr)\,dt,$$
--   the sum over $\iota_E$ being an unordered sum, where $\mathrm{convOp}(f)u=\mathrm{rightConv}(u,f)$, so that the left-hand integrand is $\bigl(\int_G u_{e,2}(gx)f(x)\,d\mu_G(x)\bigr)\overline{u_{e,1}(g)}$, and where
--   $$a_{e,ij}(t)=\int_{\mathbf{K}}\Bigl(\int_G\varphi_{e,j}(it)(kx)f(x)\,d\mu_G(x)\Bigr)\overline{\varphi_{e,i}(it)(k)}\,d\,\mathrm{maximalCompactHaar}(k),$$
--   $$\Theta_\psi(e,j,t)=\int_{\Phi_0}\mathrm{pseudoEisenstein}(\psi)(g)\,\overline{E_{e,j}(it)(g)}\,d\mu_G(g),\qquad \Theta_\varphi(e,i,t)=\int_{\Phi_0}\mathrm{pseudoEisenstein}(\varphi)(g)\,\overline{E_{e,i}(it)(g)}\,d\mu_G(g).$$
--
--   This is the Paley–Wiener case of the spectral expansion of the convolution operator $R(f)$ on the continuous part of the space of automorphic forms for $\mathrm{GL}_2$ over a number field: the inner product of the continuous components of two pseudo-Eisenstein series is expressed as a sum over the continuous-spectrum parameters of integrals along the unitary axis of local matrix coefficients of $f$ against the inner products of the pseudo-Eisenstein series with the continued Eisenstein series. It is cited by [`AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation), which treats slab profiles without the Paley–Wiener decay assumption.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_convOp_continuousProjection_pseudoEisenstein_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_pseudoEisenstein_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_matched_paleyWiener
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
    ∀
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
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (uc₁ ur₁ ue₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₁) (_huc0₁ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₁ g = 0))
      (_hur₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₁)
      (_hurc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₁)
      (_hueo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₁ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₁ : AutomorphicForm.pseudoEisenstein K φ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
      (uc₂ ur₂ ue₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₂) (_huc0₂ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₂ g = 0))
      (_hur₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₂)
      (_hurc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₂)
      (_hueo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₂ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₂ : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f ue₂ g * conj (ue₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                AutomorphicForm.pseudoEisenstein K φ g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by sorry
