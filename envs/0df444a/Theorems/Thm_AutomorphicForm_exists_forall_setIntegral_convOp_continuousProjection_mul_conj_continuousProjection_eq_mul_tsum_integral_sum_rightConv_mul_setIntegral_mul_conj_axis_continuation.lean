-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation
-- name    : AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/4d3e7cfd-71c6-5335-99f5-b3c27d820e44
-- title:
--   Continuous-spectrum Plancherel identity for R(f) on the truncation domain
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}=\mathbb{A}_K$ its adele ring, $G=\mathrm{GL}_2(\mathbb{A})$ (written `AdelicGL2 (𝓞 K) K`), $\mu_G$ the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $G$, and $\Phi_0 =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) the canonical truncation domain attached to the parameters $\alpha,\beta$. All automorphy conditions are taken with respect to the carrier pins
--   $$\mathrm{pins} = \mathtt{productionPinsOf } K\ \Phi_0\ (M \mapsto \mathtt{principalLevel } (𝓞 K)\ K\ M \sqcap \mathtt{finiteAdelicGL2Subgroup } K)\ (v \mapsto \mathtt{heckeGen } (𝓞 K)\ K\ v)\ (\mathtt{adelicBox } K),$$
--   whose measurable structure is the Borel structure `glBorel`, whose measure is $\mu_G$, whose domain is $\Phi_0$, whose central subgroup is all of $\mathbb{A}^\times$, whose level subgroups are $\mathtt{principalLevel}(M) \sqcap \mathtt{finiteAdelicGL2Subgroup}$, whose Hecke elements are the $\mathtt{heckeGen}(v)$, and whose additive measure is the adelic Haar measure conditioned on the box $\mathtt{adelicBox } K$.
--
--   **Geometric and measure-theoretic data.** Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K \subseteq G$ on which no condition is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$, $d_{1K}>0$, $d_{1K}<d_{2K}$ and a finite set $T_K \subseteq G$, subject to `hcovK`: the union $\bigcup_{x \in T_K} (\cdot\, x)$-translates of the centre-cut Siegel set $\mathtt{centreCutSiegelSet } K\ c_K\ u_K\ d_{1K}\ d_{2K}$ — the set of $g$ whose finite part is integral, whose local height at each infinite place is at least $c_K$, whose $x$-window square at each infinite place is at most $u_K^2$ and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$ — covers $G$ modulo the centre, i.e. for each $g \in G$ there are $\gamma \in \mathrm{GL}_2(K)$ and $z \in \mathbb{A}^\times$ with $\gamma g \cdot z$ in that union. Further, a Haar measure $\nu_{ZK}$ on the idele group $\mathbb{A}^\times$ (equipped with its measurable and Borel structure) and a set $\Omega_K$ which, by `hΩK`, is a fundamental domain for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_{ZK}$.
--
--   **Spectral parameters.** A finite set $S_K$ of height-one primes of $\mathcal{O}_K$; a character $\xi_K$ of the full subgroup $\top \le \mathbb{A}^\times$ with values in $\mathbb{C}^\times$, assumed continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary (`hξu`, $\lVert \xi_K(z)\rVert = 1$ for all $z$); an ideal $N \subseteq \mathcal{O}_K$ with `hN`: every prime $v$ with $v \mid N$ lies in $S_K$; and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place $w$ a number $\mathrm{card}(w)$ of representations of the row-isometry group of $K_w$ on the spaces $\mathbb{C}^{n}$.
--
--   With $\alpha_m : \mathbb{A}^\times \to \mathbb{R}^\times$ the module character obtained from `distribHaarChar` of $\mathbb{A}$ through $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and for any hypothesis $h_{\alpha m}$ that $\alpha_m$ takes strictly positive values, the assertion is the existence of a real $\kappa > 0$ — depending only on the data listed so far — such that for all of the following data the displayed identity holds.
--
--   **Cuspidal orthonormal family.** A type $\iota$, functions $b : \iota \to (G \to \mathbb{C})$ and a labelling $\mathrm{cls} : \iota \to \mathtt{HeckeEigensystem } K\ \mathbb{C}$ (a level, a nonzero-level condition and Hecke data $a_v,b_v$), with: `hb`, each $\mathrm{cls}(i)$ lies in $\mathtt{cuspClasses}$ for the pins, $\xi_K$, $N$, $S_K$ (level $N$, vanishing $a_v,b_v$ for $v \in S_K$, nonzero isotypic cusp space) and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with $\mathtt{archCutSubmodule } K\ \mathrm{tys}_K$ (the functions whose archimedean type at each place lies among the prescribed ones); `hbn`, $\int_{\Phi_0} b_i \overline{b_i}\, d\mu_G = 1$; `hbo`, $\int_{\Phi_0} b_i \overline{b_j}\, d\mu_G = 0$ for $i \ne j$; `hbs`, for every $\pi \in \mathtt{cuspClasses}$ the fibre $\{i : \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ is exactly the isotypic cusp submodule of $\pi$ cut by the archimedean types; `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function at the pins for $\xi_K$ (satisfying `LsXiMember` for the pins' structure, measure, central character and domain, cuspidal for the unipotent $\mathtt{unipotentGL2}$ and the pins' additive measure, and smooth for the finite adelic subgroup), continuous, invariant under right translation by the level subgroup $\mathrm{pins}.U\,N$, of the prescribed archimedean types and orthogonal over $\Phi_0$ to every $b_i$, vanishes almost everywhere for $\mu_G$ restricted to $\Phi_0$.
--
--   **Continuous-spectrum data.** A countable type $\iota_E$ and families $\mu,\nu : \iota_E \to \mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$ with the hypotheses: each $\mu_e,\nu_e$ is unitary, each is an idele class character (trivial on $K^\times$), each is continuous, $\mu_e \nu_e = \xi_K$ pointwise, and `_hdist`: distinct $e \ne e'$ are separated by some $z$ in the norm-one ideles (the kernel of `distribHaarChar`) at which $\mu$ or $\nu$ differ. Integers $n_e$ and sections $\varphi_{e,j,s} : G \to \mathbb{C}$ for $j < n_e$, $s \in \mathbb{C}$, subject to the hypotheses (named in the Lean `_hφE`, `_hφEK`, `_hφEf`, `_hφEjc`, `_hφEhol`, `_hφEKu`, `_hφEflat`, `_hφElev`, `_hφEty`, `_hφEon`, `_hφEspan`): each $\varphi_{e,j,s}$ is an induced section for the pair $(\mathtt{etaFst}(\mu_e,\alpha_m,h_{\alpha m},s), \mathtt{etaSnd}(\nu_e,\alpha_m,h_{\alpha m},s)) = (\mu_e \alpha_m^{s+1/2}, \nu_e \alpha_m^{-(s+1/2)})$, that is $\varphi(bg) = \eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; each is archimedean $K$-finite and $K_f$-smooth; $(s,g) \mapsto \varphi_{e,j,s}(g)$ is continuous and $s \mapsto \varphi_{e,j,s}(g)$ is entire; at each infinite place $w$ the right translates along $\mathtt{archRowIsometrySubgroup } K\ w$ all lie in one finite-dimensional space, uniformly in $s$ and $g$; the restriction to the adelic maximal compact subgroup is independent of $s$ (equal to its value at $s=0$); right invariance under $\mathtt{principalLevel}(N) \sqcap \mathtt{finiteAdelicGL2Subgroup}$; membership in $\mathtt{archCutSubmodule } K\ \mathrm{tys}_K$; orthonormality over the maximal compact subgroup, $\int_{\mathbf{K}} \varphi_{e,i,0}\overline{\varphi_{e,j,0}}\, d(\mathtt{maximalCompactHaar } K) = \delta_{ij}$; and spanning on the unitary axis: for real $t$, every continuous archimedean $K$-finite induced section for $(\mu_e,\nu_e)$ at $s = it$ which is level-$N$ invariant and of the prescribed types lies in the $\mathbb{C}$-span of the $\varphi_{e,j,it}$. Finally `_hpairs`: for every pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu' = \xi_K$, every real $t$ and every nonzero section $\varphi_0$ induced from $(\mu',\nu')$ at $s=it$ with the same regularity, level and type conditions, there is an $e \in \iota_E$ with $\mu_e = \mu'$ and $\nu_e = \nu'$ on the norm-one ideles.
--
--   **Eisenstein continuations.** Sets $O_{e,j} \subseteq \mathbb{C}$ and families $E_{e,j,s}, M_{e,j,s} : G \to \mathbb{C}$ (the Lean names the latter `NE`), subject to `_hEE`: each $O_{e,j}$ is open, preconnected, contains the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ both $s \mapsto E_{e,j,s}(g)$ and $s \mapsto M_{e,j,s}(g)$ are analytic on a neighbourhood of $O_{e,j}$; both $(s,g) \mapsto E_{e,j,s}(g)$ and $(s,g) \mapsto M_{e,j,s}(g)$ are continuous on $O_{e,j} \times G$; for $\mathrm{Re}\,s > 1/2$,
--   $$E_{e,j,s}(g) = \varphi_{e,j,s}(g) + \sum_{\xi \in K}' \varphi_{e,j,s}\bigl(w\, u(\xi)\, g\bigr),$$
--   with $w = \mathtt{adelicWeyl}$ and $u(\xi) = \mathtt{unipotentGL2}(\xi)$; and for $\mathrm{Re}\,s > 1/2$, $M_{e,j,s}(g) = \mathtt{weylIntertwiningIntegral}$ of $\varphi_{e,j,s}$ at $g$, taken against the adelic additive Haar measure.
--
--   **Test function.** A continuous, compactly supported $f : G \to \mathbb{C}$ which is factorizable ($f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ coming from a smooth compactly supported function of the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support), bi-invariant under $\mathtt{principalLevel}(N) \sqcap \mathtt{finiteAdelicGL2Subgroup}$, and archimedean bi-finite for $\mathrm{tys}_K$ (that is, $x \mapsto f(x^{-1})$ lies in $\mathtt{archCutSubmodule}$ and $f$ in $\mathtt{archDualCutSubmodule}$).
--
--   **Automorphised kernels and their spectral decompositions.** For $m = 1,2$, a measurable $\Psi_m : G \to \mathbb{C}$ vanishing outside some compact set and bounded in norm; put
--   $$\theta_m(g) = \sum^{f}_{q \in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))} \int_{\mathbb{A}^\times} \xi_K(w)^{-1}\, \bigl(\mathbf{1}_{\Phi_0}\Psi_m\bigr)\bigl(z(w)\, \gamma_q\, g\bigr)\, d\nu_{ZK}(w),$$
--   where $z(w)$ is the central scalar matrix of $w$, $\gamma_q$ the image in $G$ of a chosen representative of $q$, and the outer sum is a finsum. Functions $u^{(m)}_c, u^{(m)}_r, u^{(m)}_e$ are given with: each automorphic at the pins for $\xi_K$; the constant term of $u^{(m)}_c$ along $\mathtt{unipotentGL2}$ (taken against the pins' additive measure) vanishing $\mu_G$-almost everywhere; $u^{(m)}_r$ approximable in $L^2$ of $\mu_G$ restricted to $\Phi_0$, to within any $\varepsilon > 0$, by an automorphic element of the residual span $\mathtt{AutomorphicForm.residualSpan}$ (the span of the functions $g \mapsto \chi(\det g)$ with $\chi^2 = \xi_K$); $u^{(m)}_e$ orthogonal over $\Phi_0$ to every automorphic $h$ whose constant term vanishes almost everywhere or which lies in that residual span; and the decomposition $\theta_m = u^{(m)}_c + u^{(m)}_r + u^{(m)}_e$ almost everywhere for $\mu_G$ restricted to $\Phi_0$.
--
--   **Conclusion.** Under all of the above,
--   $$\int_{\Phi_0} \bigl(\mathtt{convOp } K\, f\, u^{(2)}_e\bigr)(g)\, \overline{u^{(1)}_e(g)}\, d\mu_G(g) = \kappa \sum_{e \in \iota_E}' \int_{\mathbb{R}} \sum_{i,j < n_e} A^{e}_{j,i}(t)\, \Theta^{(2)}_{e,j}(t)\, \overline{\Theta^{(1)}_{e,i}(t)}\, dt,$$
--   where $\mathtt{convOp } K\, f\, u = \mathtt{rightConv } K\, u\, f$ is the right convolution $g \mapsto \int_G u(gx) f(x)\, d\mu_G(x)$,
--   $$A^{e}_{j,i}(t) = \int_{\mathbf{K}} \bigl(\mathtt{rightConv } K\, \varphi_{e,j,it}\, f\bigr)(k)\, \overline{\varphi_{e,i,it}(k)}\, d(\mathtt{maximalCompactHaar } K)(k)$$
--   is taken over the adelic maximal compact subgroup, and
--   $$\Theta^{(m)}_{e,l}(t) = \int_{\Phi_0} \theta_m(g)\, \overline{E_{e,l,it}(g)}\, d\mu_G(g),$$
--   the pairings being formed with the automorphised kernels $\theta_2$ and $\theta_1$ written out explicitly, and not with $u^{(m)}_e$. The sum over $e$ is a $\mathbb{C}$-valued tsum, the integral in $t$ is over $\mathbb{R}$, and $\kappa$ is coerced into $\mathbb{C}$.
--
--   This is the continuous-spectrum (Eisenstein) block of the spectral expansion of the right convolution operator $R(f)$ on $L^2(\mathrm{GL}_2(K)\backslash \mathrm{GL}_2(\mathbb{A}),\xi)$, read on the canonical truncation domain: the Plancherel formula for the continuous part expresses the pairing $\langle R(f)u^{(2)}_e, u^{(1)}_e\rangle$ as an integral over the unitary axis of local matrix coefficients of the induced representations against the pairings of the automorphised kernels with the Eisenstein series. It feeds the assembly of the full spectral expansion in [`AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation
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
      (Ψ₁ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨ₁m : Measurable Ψ₁)
      (_hΨ₁c : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ₁ y = 0)
      (_hΨ₁b : ∃ M : ℝ, ∀ y, ‖Ψ₁ y‖ ≤ M)
      (Ψ₂ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨ₂m : Measurable Ψ₂)
      (_hΨ₂c : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ₂ y = 0)
      (_hΨ₂b : ∃ M : ℝ, ∀ y, ‖Ψ₂ y‖ ≤ M)
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
      (_hsum₁ : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₁
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
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
      (_hsum₂ : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₂
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f ue₂ g * conj (ue₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                (fun g : AdelicGL2 (𝓞 K) K =>
              ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
                  (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₂
                    (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                (fun g : AdelicGL2 (𝓞 K) K =>
              ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
                  (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₁
                    (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by sorry
