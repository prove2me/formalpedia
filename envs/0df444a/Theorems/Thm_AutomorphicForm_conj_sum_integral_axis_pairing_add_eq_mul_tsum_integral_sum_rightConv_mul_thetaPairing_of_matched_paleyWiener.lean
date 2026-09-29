-- Prove2me | Theorems.Thm_AutomorphicForm_conj_sum_integral_axis_pairing_add_eq_mul_tsum_integral_sum_rightConv_mul_thetaPairing_of_matched_paleyWiener
-- name    : AutomorphicForm.conj_sum_integral_axis_pairing_add_eq_mul_tsum_integral_sum_rightConv_mul_thetaPairing_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7ce972ea-38cd-5cd8-a3be-21f3440179b5
-- title:
--   Axis pairing of (φ,R(f)ψ) as Eisenstein-coefficient sum
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$, and $D:=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the canonical truncation domain in $\mathrm{GL}_2(\mathbb{A}_K)$, equipped with the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2$ of the adeles; `maximalCompactHaar K` is the Haar measure on the adelic maximal compact subgroup `adelicMaximalCompact K` (finite part integral, archimedean parts row isometries), and $v:=((\mathrm{adelicAddHaar}\ (𝓞\ K)\ K)(\mathrm{adelicBox}\ K)).\mathrm{toReal}$ is the volume of the adelic box.
--
--   **Siegel covering datum.** A set $\Phi_K$ of adelic $\mathrm{GL}_2$ points, reals $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$, $0<d_{1K}$, $d_{1K}<d_{2K}$, and a finite set $T_K$ of adelic $\mathrm{GL}_2$ points are given such that $\bigcup_{x\in T_K}(\cdot\,x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` satisfies `CoversModCentre K`: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central idele $z$ with $\gamma g z$ in that union. The centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean local heights are $\ge c_K$ at each infinite place, whose $x$-window squares are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$.
--
--   **Measure-theoretic data on the ideles.** The idele unit group carries a measurable and Borel structure, a Haar measure $\nu_{Z K}$, and a set $\Omega_K$ which is a fundamental domain (`IsFundamentalDomain`) for the range of $K^\times\to(\mathbb{A}_K)^\times$ acting on it.
--
--   **Central character and level.** $S_K$ is a finite set of height-one primes of $\mathcal{O}_K$; $\xi_K$ is a monoid homomorphism from the full subgroup of idele units to $\mathbb{C}^\times$, continuous as a function of the idele ($h\xi c$), trivial on the image of $K^\times$ ($h\xi t$), and of absolute value $1$ everywhere ($h\xi u$); $N$ is an ideal of $\mathcal{O}_K$ with every prime dividing $N$ in $S_K$ ($hN$); $\mathrm{tys}_K$ is an `ArchTypeFamily K`, cutting out the submodule `archCutSubmodule K tysK` of functions of prescribed archimedean $K$-types. Writing $\alpha_m$ for the homomorphism from idele units to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ through $\mathbb{R}_{\ge0}\to\mathbb{R}$, the statement is made for every hypothesis $h\alpha_m$ that all values of $\alpha_m$ are positive; then `etaFst μ αm hαm s` $=\mu\cdot\alpha_m^{\,s+1/2}$ and `etaSnd ν αm hαm s` $=\nu\cdot\alpha_m^{-(s+1/2)}$.
--
--   All automorphic notions are taken with respect to the carrier pins $P:=$ `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose domain is $D$, whose central subgroup $P.Z$ is the whole idele unit group, whose level subgroups are $\Gamma(M)\cap\ker(\text{archimedean projection})$, whose Hecke generators are `heckeGen`, and whose additive measure is the adelic additive Haar measure conditioned on the adelic box.
--
--   **Discrete cuspidal basis.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` are given with: $hb$, each $\mathrm{cls}\,i$ lies in `cuspClasses K P ξK N SK` (level $N$, all eigenvalues $a_v,b_v$ vanishing at $v\in S_K$, nonzero isotypic cuspidal submodule) and $b\,i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}\,i$ intersected with `archCutSubmodule K tysK`; $hbn$, $\int_D b_i\,\overline{b_i}=1$; $hbo$, $\int_D b_i\,\overline{b_j}=0$ for $i\ne j$; $hbs$, for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ is the isotypic submodule of $\pi$ intersected with `archCutSubmodule K tysK`; and $hbc$, completeness: any $\varphi$ that is a smooth cuspidal automorphic function at $P$ for $\xi_K$, continuous, right invariant under $P.U\,N$, contained in `archCutSubmodule K tysK` and orthogonal over $D$ to every $b_i$, vanishes almost everywhere on $D$.
--
--   **Continuous-spectrum families.** A countable type $\iota_E$ and characters $\mu,\nu:\iota_E\to((\mathbb{A}_K)^\times\to\mathbb{C}^\times)$ are given with each $\mu e,\nu e$ unitary (`IsUnitaryChar`), trivial on $K^\times$ (`IsIdeleClassChar`), continuous, with $\mu e\cdot\nu e=\xi_K$ pointwise, and distinct pairs separated by a norm-one idele ($\_hdist$). For each $e$, $n_E e\in\mathbb{N}$ and functions $\varphi_{E}(e,j,s,\cdot)$, $j\in\mathrm{Fin}(n_Ee)$, satisfy: each is an induced section for the characters $(\mathrm{etaFst}(\mu e)\,s,\mathrm{etaSnd}(\nu e)\,s)$, i.e. $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup; they are archimedean $K$-finite, $K_f$-smooth, jointly continuous in $(s,g)$, holomorphic in $s$ for fixed $g$, with right translates under each `archRowIsometrySubgroup K w` lying in a fixed finite-dimensional space uniformly in $s$ and $g$; they are flat on the maximal compact ($\varphi_E e\,j\,s\,k=\varphi_E e\,j\,0\,k$), right invariant under $\Gamma(N)\cap\ker(\text{arch})$, contained in `archCutSubmodule K tysK`, orthonormal on the adelic maximal compact at $s=0$ ($\_h\varphi Eon$), spanning: any section at $s=it$ for $(\mu e,\nu e)$ which is continuous, archimedean $K$-finite, level invariant and of the prescribed types lies in the span of the $\varphi_E e\,j\,(it)$ ($\_h\varphi Espan$); and $\_hpairs$, every nonzero such section for an arbitrary admissible pair $(\mu',\nu')$ of unitary idele class characters with $\mu'\nu'=\xi_K$ agrees in its character pair, on the norm-one ideles, with some $(\mu e,\nu e)$.
--
--   **Eisenstein continuations of the $\varphi_E$.** Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j,\cdot,\cdot)$, $N_E(e,j,\cdot,\cdot)$ are given; the hypothesis $\_hEE$ (nine clauses) requires $O_E(e,j)$ open and preconnected, containing the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$, for each $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ analytic on a neighbourhood of $O_E(e,j)$, joint continuity of $(s,g)\mapsto E_E$ and of $(s,g)\mapsto N_E$ on $O_E(e,j)\times\mathrm{univ}$, and for $\mathrm{Re}\,s>1/2$ the identities $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum'_{\xi\in K}\varphi_E(e,j,s,\,w\,u(\xi)\,g)$ with $w=$ `adelicWeyl` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$, and $N_E(e,j,s,\cdot)=$ `weylIntertwiningIntegral` of $\varphi_E(e,j,s,\cdot)$ against the adelic additive Haar measure, that is $g\mapsto\int \varphi_E(e,j,s,\,w^{-1}u(x)g)\,dx$.
--
--   **Test function.** $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ is continuous with compact support, factorizable (`IsFactorizableTestFn`: $f(g)=f_\infty(\text{arch part})\,f_{\mathrm{fin}}(\text{finite part})$ with $f_\infty$ given by a smooth compactly supported function of the matrix entries and $f_{\mathrm{fin}}$ locally constant with compact support), bi-invariant under $\Gamma(N)\cap\ker(\text{arch})$, and archimedean bi-finite for $\mathrm{tys}_K$ (`IsArchBiFinite`: $g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`).
--
--   **Paley–Wiener datum.** A finite type $\iota_P$, characters $\mu_P,\nu_P:\iota_P\to((\mathbb{A}_K)^\times\to\mathbb{C}^\times)$ with all $\mu_P e,\nu_P e$ unitary idele class characters, $\mu_P$ and $\nu_P$ continuous, $\mu_P e(z)\nu_P e(z)=\xi_K(z)$ for $z$ in the central subgroup $P.Z$, a map $r_P:\iota_P\to\iota_P$ with $\mu_P(r_Pe)=\nu_Pe$ and $\nu_P(r_Pe)=\mu_Pe$, and distinct indices separated by a norm-one idele. Families $\hat\varphi=\varphi_f$ and $\hat\psi=\psi_f$ on $\iota_P\times\mathbb{C}$ are induced sections for $(\mathrm{etaFst}(\mu_Pe)s,\mathrm{etaSnd}(\nu_Pe)s)$, jointly continuous in $(s,g)$ and holomorphic in $s$; $\psi_f$ is moreover archimedean $K$-finite, $K_f$-smooth, and has uniformly finite-dimensional archimedean row-isometry translates. The decay hypotheses $\_h\varphi dec$ and $\_h\psi dec$ require, for each index, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$, an integrable bounded majorant $m$ on $\mathbb{R}$ with $(1+|t|)^n\|\varphi_f e(\sigma'+it)g\|\le m(t)$, respectively the same for $\psi_f$, for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$.
--
--   **Slab profiles and matching.** Functions $\varphi,\psi$ satisfy [`AutomorphicForm.IsSlabProfile`](def/AutomorphicForm_SlabProfile.html#L17) for the central subgroup $P.Z$ and $\xi_K$: measurability, invariance under left multiplication by unipotents and by global Borel points, the central transformation rule by $\xi_K$, boundedness on every slab of idele determinant norms in $[d_1,d_2]$ with $d_1>0$, and a height band. The hypotheses $\_h\varphi rep$, $\_h\psi rep$ state that for every real $\sigma'$ and every $g$, $\varphi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\varphi_f e(\sigma'+it)g\,dt$ and likewise for $\psi$ with $\psi_f$. Maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ satisfy $\_hem$: $\mu_Pi=\mu(\mathrm{em}\,i)\cdot\mathrm{normPowChar}\ K\,(\tau i)$ and $\nu_Pi=\nu(\mathrm{em}\,i)\cdot(\mathrm{normPowChar}\ K\,(\tau i))^{-1}$, where `normPowChar K t` is $x\mapsto\|x\|^{\,it}$.
--
--   **Continuations of $\psi_f$ and growth.** Sets $O_\psi(i)$ and functions $E_\psi(i,\cdot,\cdot)$, $N_\psi(i,\cdot,\cdot)$ satisfy the same nine clauses as $\_hEE$, with $\psi_f i$ in place of $\varphi_E e\,j$. The hypotheses $\_hN\psi$ and $\_hNE$ give, for each $i$ and each $(e,j)$, constants $A$ and $n$ with $\|N_\psi(i,it,k)\|\le A(1+|t|)^n$, respectively $\|N_E(e,j,it,k)\|\le A(1+|t|)^n$, for all real $t$ and all $k$ in the adelic maximal compact.
--
--   **Coefficient hypotheses.** A constant $\kappa''>0$ is given, together with three identities for the pairings over $D$ of the pseudo-Eisenstein series [`AutomorphicForm.pseudoEisenstein K`](def/AutomorphicForm_SlabProfile.html#L32) (that is, $g\mapsto\varphi(g)+\sum'_{\beta\in K}\varphi(w\,u(\beta)g)$) against the conjugates of the $E_E$: for all $i\in\iota_P$, $j\in\mathrm{Fin}(n_E(\mathrm{em}\,i))$ and $t\in\mathbb{R}$,
--   $$\int_D (\text{pseudoEisenstein }\varphi)\,\overline{E_E(\mathrm{em}\,i,j,i(t+\tau i))}=\kappa''\Big(\int \varphi_f i(it)(k)\,\overline{\varphi_E(\mathrm{em}\,i,j,i(t+\tau i))(k)}\,dk+\int \varphi_f(r_Pi)(-it)(k)\,\overline{v^{-1}N_E(\mathrm{em}\,i,j,i(t+\tau i))(k)}\,dk\Big),$$
--   the inner integrals being over the adelic maximal compact ($\_h\Theta\varphi$); the same identity with $\psi,\psi_f$ in place of $\varphi,\varphi_f$ ($\_h\Theta\psi$); and $\_h\Theta\psi0$, that $\int_D(\text{pseudoEisenstein }\psi)\,\overline{E_E(e,j,it)}=0$ whenever $e$ is not in the image of $\mathrm{em}$.
--
--   **Conclusion.** The complex conjugate of
--   $$\sum_{i\in\iota_P}\int_{\mathbb{R}}\Big(\int \varphi_f i(it)(k)\,\overline{(\mathrm{convOp}\ K\ f\,\varphi_f\text{-partner})}\,dk\Big)dt$$
--   with the integrand written out exactly as in the Lean statement, namely
--   $$\overline{\sum_{i\in\iota_P}\int_{\mathbb{R}}\Big(\int \varphi_f i(it)(k)\,\overline{\mathrm{convOp}\ K\ f\,(\psi_f i(it))(k)}\,dk+v^{-1}\int \varphi_f i(it)(k)\,\overline{\mathrm{convOp}\ K\ f\,(N_\psi(r_Pi)(-it))(k)}\,dk\Big)dt},$$
--   where `convOp K f u` $=$ `rightConv K u f` and both inner integrals are taken over the adelic maximal compact against `maximalCompactHaar K`, equals
--   $$\frac{1}{2(\kappa'')^2}\sum_{e\in\iota_E}{}'\int_{\mathbb{R}}\sum_{i,j\in\mathrm{Fin}(n_Ee)}\Big(\int \mathrm{rightConv}\ K\,(\varphi_E(e,j,it))\,f\,(k)\,\overline{\varphi_E(e,i,it)(k)}\,dk\Big)\cdot\Big(\int_D(\text{pseudoEisenstein }\psi)\,\overline{E_E(e,j,it)}\Big)\cdot\overline{\Big(\int_D(\text{pseudoEisenstein }\varphi)\,\overline{E_E(e,i,it)}\Big)}\,dt,$$
--   the sum over $\iota_E$ being an unconditional sum (`tsum`), the pairings over $D$ being taken against `adelicGLHaar (Fin 2) (𝓞 K) K` restricted to $D$, and the factor $\tfrac{1}{2(\kappa'')^2}$ entering as the real number $1/(2(\kappa'')^2)$ coerced to $\mathbb{C}$.
--
--   This is the step that converts the axis pairing of a matched Paley–Wiener pair $(\varphi,R(f)\psi)$ — the pairing built from the sections $\varphi_f$, $\psi_f$ and the Weyl intertwining continuation $N_\psi$ on the unitary axis — into an expansion over the continuous spectrum in which the $\varphi_E$-matrix coefficients of right convolution by $f$ are multiplied by products of Eisenstein coefficients of the two pseudo-Eisenstein series. It is the final rewriting used by [`AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_pseudoEisenstein_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_pseudoEisenstein_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_matched_paleyWiener), and is obtained from the symmetric two-term fold [`AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched`](thm.html#AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched) together with the coefficient identities $\_h\Theta\varphi$, $\_h\Theta\psi$ and $\_h\Theta\psi0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_conj_sum_integral_axis_pairing_add_eq_mul_tsum_integral_sum_rightConv_mul_thetaPairing_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.conj_sum_integral_axis_pairing_add_eq_mul_tsum_integral_sum_rightConv_mul_thetaPairing_of_matched_paleyWiener
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
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (_hNψ : ∀ (i : ιP), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (_hNE : ∀ (e : ιE) (j : Fin (nE e)), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (κ'' : ℝ) (_hκ'' : 0 < κ'')
      (_hΘφ : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K φ g * conj (EE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
          (κ'' : ℂ) * ((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, φf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
              conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)))
      (_hΘψ0 : ∀ (e : ιE), (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ),
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0)
      (_hΘψ : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K ψ g * conj (EE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
          (κ'' : ℂ) * ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
              conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))),
    conj (∑ i : ιP, ∫ t : ℝ,
        ((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
          (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) =
      ((1 / (2 * κ'' ^ 2) : ℝ) : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                AutomorphicForm.pseudoEisenstein K φ g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by sorry
