-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/2b09f0ce-366e-5260-b6e2-d9cb9c5c4949
-- title:
--   Integrated spectral expansion of the truncated σ-twisted continuous kernel
-- statement:
--   Throughout, $K\subseteq L$ are number fields ($L$ an algebra over $K$), $\mathbb{A}=$ `AdeleRing (𝓞 L) L`, and `AdelicGL2 (𝓞 L) L` $=\mathrm{GL}_2(\mathbb{A})$ carries its Borel $\sigma$-algebra `glBorel` and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   **Geometric and measure-theoretic data.** Reals $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`); a set $\Phi_L\subseteq\mathrm{GL}_2(\mathbb{A})$ contained in the slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$ (`hΦs`, the norm being [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), i.e. the module character `distribHaarChar` of $\mathbb{A}$) which is a fundamental domain for the range of `globalPoints (𝓞 L) L` (the image of $\mathrm{GL}_2(L)$) acting on the slab-restricted Haar measure (`hΦ`); a measurable structure and Borel space structure on $\mathbb{A}^\times$, a Haar measure $\nu_{Z,L}$ on $\mathbb{A}^\times$ and a set $\Omega_L$ which is a fundamental domain for the range of $L^\times\to\mathbb{A}^\times$ in $(\mathbb{A}^\times,\nu_{Z,L})$ (`hΩL`); a Galois descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28) (a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}$, compatible with $L\to\mathbb{A}$ and continuous), and $\sigma\in L\simeq_{\mathrm{alg}[K]}L$.
--
--   **Character, level and place data.** A finite set $S_L$ of finite places of $L$ whose membership depends only on the place of $K$ below (`hSL`, via `HeightOneSpectrum.under (𝓞 K)`); a homomorphism $\xi_L$ from the top subgroup of $\mathbb{A}^\times$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`) and trivial on principal ideles (`hξt`); an ideal $N$ of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`); an archimedean type family $\mathrm{tys}_L$ (`ArchTypeFamily L`: a number of types at each infinite place together with representations of the row-isometry subgroups).
--
--   **Truncation domain data.** Reals $c,u,d_1,d_2$ with $c>0$ (`hc`); a compact set $T_c$ (`hTc`); a set $\Phi_0$ contained in the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (`hΦ₀S`), contained in the same slab (`hΦ₀s`), and again a fundamental domain for the image of $\mathrm{GL}_2(L)$ on the slab-restricted Haar measure (`hΦ₀`).
--
--   **Weight and twisted character.** A real $w$ with $\|\xi_L(z)\|=\|z\|^{w}$ for all ideles $z$ (`hξw`), and a homomorphism $\xi'$ with $\xi'(z)=\xi_L(D.\mathrm{unitsAct}\,\sigma\,(z))$ for all $z$ (`hξ'`), i.e. $\xi'=\xi_L\circ\sigma_{\mathbb{A}}$.
--
--   After these, $\alpha_m$ is introduced as the $\mathbb{R}^\times$-valued character of $\mathbb{A}^\times$ obtained from `distribHaarChar` via $\mathbb{R}_{\ge0}\to\mathbb{R}$, and the adeles are given the measurable structure `adeleBorel (𝓞 L) L`. The assertion is: assuming $\alpha_m$ takes strictly positive values (`hαm`), there exists $\kappa\in\mathbb{R}$ with $\kappa>0$ such that for all the following data the conclusion below holds; the constant $\kappa$ is chosen before, hence independently of, all data listed from here on.
--
--   **Cuspidal orthonormal system.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem L ℂ` (a level ideal, nonzero, with coefficient families $a,b$ indexed by finite places). All spectral notions are taken at the carrier pins `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, whose fundamental domain is $\Phi_L$, whose central subgroup is the whole of $\mathbb{A}^\times$, whose level subgroups are `levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L`, whose Hecke generators are `heckeGen (𝓞 L) L w`, and whose adelic measure is additive Haar conditioned to `adelicBox L`. The hypotheses are: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses` for $\xi_L,N,S_L$ (level $=N$, $a_v=b_v=0$ for $v\in S_L$, nonzero isotypic cusp submodule) and $b\,i$ lies in the corresponding `isotypicCuspSubmodule` intersected with `archCutSubmodule L tysL`; `hb₁`, $\int_{\Phi_L}b_i\overline{b_i}=1$; `hb₀`, $\int_{\Phi_L}b_i\overline{b_j}=0$ for $i\neq j$; `hbs`, for each class $\pi$ the fibre $\{i:\mathrm{cls}\,i=\pi\}$ is finite and the $b_i$ over that fibre span the cut isotypic submodule of $\pi$; `hbc`, completeness — any $\psi$ which is a smooth cuspidal automorphic function at the pins for $\xi_L$, continuous, right invariant under the level subgroup at $N$, in `archCutSubmodule L tysL` and orthogonal on $\Phi_L$ to every $b_i$, vanishes almost everywhere for the Haar measure restricted to $\Phi_L$.
--
--   **Eisenstein data.** A countable type $\iota_E$ and families $\mu_E,\nu_E:\iota_E\to(\mathbb{A}^\times\to\mathbb{C}^\times)$, with: `_hμ`, `_hν`, each character unitary ($\|\mu_E(e)(x)\|=1$, likewise $\nu_E$); `_hμic`, `_hνic`, each trivial on principal ideles; `_hμc`, `_hνc`, continuity of the associated $\mathbb{C}$-valued functions; `_hμν`, $\mu_E(e)(z)\,\nu_E(e)(z)\,\|z\|^{w}=\xi'(z)$ for all $z$; `_hdist`, for $e\neq e'$ some norm-one idele separates the pairs. Natural numbers $n_E(e)$ and sections $\varphi_E(e):\mathrm{Fin}\,n_E(e)\to\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ subject to: `_hφE`, each $\varphi_E(e)_j(s)$ is an induced section for the pair $(\mathrm{etaFst}\,\mu_E(e)\,\alpha_m\,s,\ \mathrm{etaSnd}\,\nu_E(e)\,\alpha_m\,s)=(\mu_E(e)\|\cdot\|^{s+1/2},\ \nu_E(e)\|\cdot\|^{-(s+1/2)})$, i.e. $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK`, archimedean $K$-finiteness (`IsArchKFinite L`: at each infinite place the predicate `RightTranslatesSpanFinite` for `archRowIsometrySubgroup L`); `_hφEf`, smoothness as a vector for the finite adelic subgroup (`IsKfSmooth L`); `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each $g$; `_hφEKu`, for each $e,j$ and each infinite place, a finite-dimensional subspace of functions on `archRowIsometrySubgroup L` containing all right translates; `_hφEflat`, $\varphi_E(e)_j(s)(k)=\varphi_E(e)_j(0)(k)$ for $k$ in `adelicMaximalCompact L`; `_hφElev`, right invariance under `principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`; `_hφEty`, membership in `archCutSubmodule L tysL`; `_hφEon`, orthonormality $\int_{\mathrm{adelicMaximalCompact}}\varphi_E(e)_i(0)\overline{\varphi_E(e)_j(0)}=\delta_{ij}$ for `maximalCompactHaar L`; `_hφEspan`, for each $e$, each $t\in\mathbb{R}$ and each $\varphi_0$ which is an induced section at $s=it$ for $(\mu_E(e),\nu_E(e))$, continuous, archimedean $K$-finite, invariant under the principal level at $N$ and of the prescribed archimedean type, $\varphi_0$ lies in the $\mathbb{C}$-span of the $\varphi_E(e)_j(it)$; `_hpairs`, completeness of the family of pairs — for any unitary, idele-class, continuous pair $(\mu',\nu')$ with $\mu'\nu'\|\cdot\|^{w}=\xi'$ and any nonzero $\varphi_0$ satisfying the same five conditions at $s=it$ for $(\mu',\nu')$, there is $e$ with $\mu_E(e)=\mu'$ and $\nu_E(e)=\nu'$ on the norm-one ideles. Finally sets $O_E(e)_j\subseteq\mathbb{C}$ and families $E_E,N_E$ with the nine-clause hypothesis `_hEE`: each $O_E(e)_j$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$, $s\mapsto E_E(e)_j(s)(g)$ and $s\mapsto N_E(e)_j(s)(g)$ are analytic on a neighbourhood of $O_E(e)_j$; both are continuous on $O_E(e)_j\times\mathrm{univ}$ in $(s,g)$; for $\mathrm{Re}\,s>1/2$ one has the Eisenstein expansion $E_E(e)_j(s)(g)=\varphi_E(e)_j(s)(g)+\sum_{\xi\in L}\varphi_E(e)_j(s)\big(\mathrm{adelicWeyl}\cdot\mathrm{unipotentGL2}(\xi)\cdot g\big)$ and $N_E(e)_j(s)(g)=\mathrm{weylIntertwiningIntegral}$ of $\varphi_E(e)_j(s)$ at $g$, taken with adelic additive Haar measure.
--
--   **Test function.** A function $\varphi:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$, continuous (`_hφ`) with compact support (`_hφc`), factorizable (`IsFactorizableTestFn L`: $\varphi(g)=f_\infty(\mathrm{glArch}\,g)f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ smooth in the matrix entries and compactly supported, $f_{\mathrm{fin}}$ locally constant and compactly supported), bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, and archimedeanly bi-finite for $\mathrm{tys}_L$ (`IsArchBiFinite L`: $x\mapsto\varphi(x^{-1})$ lies in `archCutSubmodule` and $\varphi$ in `archDualCutSubmodule`).
--
--   **Conclusion.** There exists $R_0\in\mathbb{R}$ such that for every $R\ge R_0$ the following four assertions hold. Write $\Lambda^{R}$ for the truncation [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) at the pins' adelic measurable structure and measure, with unipotent embedding $t\mapsto\mathrm{unipotentGL2}(t)$, height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) and parameter $e^{R}$, i.e. $\Lambda^{R}\psi(g)=\psi(g)-\mathbf 1_{\{\mathrm{height}>e^R\}}(g)\cdot(\text{constant term of }\psi)(g)$, the constant term being the unipotent integral for the conditioned adelic measure; write $\sigma_{\mathbb{A}}^{-1}$ for `sigmaAdelicAct K L D σ.symm`, $V_Z:=\nu_{Z,L}\big(\Omega_L\cap\{z:\|\det(\mathrm{centralScalar}\,z)\|\in[\alpha,\beta]\}\big)$ and $V_0:=\mathrm{adelicGLHaar}(\Phi_0)$, both as real numbers. For each $x$ put
--   $$\mathcal K_1(x)=\Lambda^{R}\Big(y\mapsto\textstyle\sum^{f}_{q\in\mathrm{GL}_2(L)/Z}\int_{\mathbb{A}^\times}\xi_L(z)\,\varphi\big(x^{-1}\,\mathrm{globalPoints}(q.\mathrm{out})\,\sigma_{\mathbb{A}}^{-1}(\mathrm{centralScalar}(z)\,y)\big)\,d\nu_{Z,L}(z)\Big)(x),$$
--   where $\sum^f$ is the finite sum over the quotient of $\mathrm{GL}_2(L)$ by its centre,
--   $$\mathcal K_2(x)=\Lambda^{R}\Big(y\mapsto V_Z\cdot\textstyle\sum'_{\Psi\in\mathrm{cuspClasses}}\ \sum^{f}_{\{i:\mathrm{cls}\,i=\Psi\}}\big(\mathrm{twistedConvOp}\,K\,L\,D\,\sigma\,\varphi\,(b_i)\big)(x)\,\overline{b_i(y)}\Big)(x),$$
--   where `twistedConvOp K L D σ φ (b i)` is the right convolution `rightConv L` of the $\sigma$-transform `sigmaSectionActOn K L D σ (b i)` with $\varphi$, and
--   $$\mathcal K_3(x)=\Lambda^{R}\Big(y\mapsto \frac{V_Z}{V_0}\,\textstyle\sum^{f}_{\chi}\big(\mathrm{twistedConvOp}\,K\,L\,D\,\sigma\,\varphi\,(\mathrm{chiDet}\,\chi)\big)(x)\,\mathrm{chiDet}(\chi^{-1})(y)\Big)(x),$$
--   the finite sum running over those characters $\chi$ of $\mathbb{A}^\times$ with $\chi(z)^2=\xi_L(z)$ for all $z$ (`SquaresToXi`), trivial on principal ideles and continuous, with $\mathrm{chiDet}\,\chi(g)=\chi(\det g)$. For each $e$ and $t\in\mathbb{R}$ put
--   $$F_e(t)=\sum_{i,j}\Big(\int_{\mathrm{adelicMaximalCompact}}\mathrm{rightConv}\,L\,\big(g\mapsto\varphi_E(e)_j(it)(g)\,\|\det g\|^{w/2}\big)\,\varphi\,(k)\ \overline{\varphi_E(e)_i(it)(k)}\,d\,\mathrm{maximalCompactHaar}\Big)\cdot\int_{\Phi_0}\Lambda^{R}\big(E_E(e)_i(it)\big)(x)\ \overline{\Lambda^{R}\big(y\mapsto E_E(e)_j(it)(\sigma_{\mathbb{A}}^{-1}y)\big)(x)}\,dx,$$
--   the sums being over $i,j\in\mathrm{Fin}\,n_E(e)$ and the outer integral taken for `adelicGLHaar`.
--
--   Then: (i) $x\mapsto\mathcal K_1(x)-\mathcal K_2(x)-\mathcal K_3(x)$ is integrable on $\Phi_0$ for `adelicGLHaar`; (ii) for every $e\in\iota_E$ the function $t\mapsto F_e(t)$ is integrable on $\mathbb{R}$; (iii) the function $e\mapsto\int_{\mathbb{R}}\|F_e(t)\|\,dt$ is summable over $\iota_E$; and (iv)
--   $$\int_{\Phi_0}\big(\mathcal K_1(x)-\mathcal K_2(x)-\mathcal K_3(x)\big)\,dx=\kappa\cdot\sum'_{e\in\iota_E}\int_{\mathbb{R}}F_e(t)\,dt .$$
--
--   This is the continuous-spectrum block of the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a number field: after the cuspidal and residual kernels are subtracted from the twisted geometric kernel, the truncated remainder integrated over a Siegel-covered slab fundamental domain is expressed, up to a positive constant independent of the spectral data and of the test function, as a convergent sum over pairs of unitary Hecke characters of integrals along the unitary axis of matrix coefficients against truncated Eisenstein inner products. It is the form of the expansion used by [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub), where the truncation parameter is let tend to infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
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
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ))
    (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ = ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ κ : ℝ, 0 < κ ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
        b i ∈ isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
      (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
      (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
      (hbs : ∀ π ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
        {i | cls i = π}.Finite ∧
        Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
      (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
        IsSmoothCuspAutomorphicFnAt L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
        Continuous ψ →
        (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
        ψ ∈ archCutSubmodule L tysL →
        (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
        ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0)
      (ιE : Type) [Countable ιE]
      (μE νE : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μE e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (νE e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μE e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (νE e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ),
        ((μE e z : ℂˣ) : ℂ) * ((νE e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μE e z ≠ μE e' z ∨ νE e z ≠ νE e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm s) (etaSnd (νE e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite L (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth L (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 L) L), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace L), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φE e j s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
        φE e j s (k : AdelicGL2 (𝓞 L) L) = φE e j 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule L tysL)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst (μE e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νE e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μE' νE' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μE' → IsUnitaryChar (𝓞 L) L νE' →
        IsIdeleClassChar (𝓞 L) L μE' → IsIdeleClassChar (𝓞 L) L νE' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μE' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((νE' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ((μE' z : ℂˣ) : ℂ) * ((νE' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μE' αm hαm ((t : ℂ) * Complex.I)) (etaSnd νE' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μE e z = μE' z ∧ νE e z = νE' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        EE e j s g = φE e j s g + ∑' ξ : L, φE e j s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        NE e j s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φE e j s) g))
      (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ),
      IsFactorizableTestFn L φ →
      IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
      IsArchBiFinite L tysL φ →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ (k : AdelicGL2 (𝓞 L) L) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
            (∫ x in Φ₀,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)))) ∧
      (Summable fun e : ιE => ∫ t : ℝ, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ (k : AdelicGL2 (𝓞 L) L) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
            (∫ x in Φ₀,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L))‖) ∧
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      AutomorphicForm.sigmaAdelicAct K L D σ.symm
                        (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (fun g : AdelicGL2 (𝓞 L) L => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) φ (k : AdelicGL2 (𝓞 L) L) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L)) *
            (∫ x in Φ₀,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
