-- Prove2me | Theorems.Thm_AutomorphicForm_norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le
-- name    : AutomorphicForm.norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/95f1be37-404f-52a4-8f46-07c4cf7c899b
-- title:
--   Stability of the Eisenstein coefficient form of R(f)
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal{O}_K$, and $\mathrm{GL}_2(\mathbb{A}_K)$ denotes `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring, carrying its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`.
--
--   **Ambient data.** Real numbers $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`); a set $\Phi_K$ of adelic matrices; real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`), $d_{1K}<d_{2K}$ (`hdK`); a finite set $T_K$ of adelic matrices such that the union of the right translates $S\cdot x$, $x\in T_K$, of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` (those $g$ whose finite part is integral, whose local height at each infinite place is at least $c_K$, whose window quantity `xWindowSq` at each infinite place is at most $u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo rational points and the centre, in the sense of `CoversModCentre`: for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\, g\, z$ (the central scalar $z$) in that union (`hcovK`). Further: a Haar measure $\nu_{Z K}$ on the idele group $\mathbb{A}_K^\times$ and a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{Z K}$ (`hΩK`); a finite set $S_K$ of finite places; a character $\xi_K$ of the full subgroup $\top\le\mathbb{A}_K^\times$ with values in $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N\subseteq\mathcal{O}_K$ such that every finite place dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$ (`ArchTypeFamily K`), which cuts out the submodule `archCutSubmodule K tysK`, the intersection over the infinite places $w$ of the sum of the type submodules attached to the finitely many representations $\mathrm{tys}_K.\mathrm{rep}\,w\,i$ of the row-isometry group at $w$.
--
--   Write $\alpha_m$ for the homomorphism $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$; the hypothesis `hαm` asserts $\alpha_m(x)>0$ for all $x$. For a character $\mu$ and $s\in\mathbb{C}$, `etaFst μ αm hαm s` is $\mu\cdot\alpha_m^{\,s+1/2}$ and `etaSnd ν αm hαm s` is $\nu\cdot\alpha_m^{-(s+1/2)}$. Let `pins` denote the carrier package `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the domain `canonicalTruncationDomain K α β`, central subgroup $\top$, level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators `heckeGen (𝓞 K) K v`, and on $\mathbb{A}_K$ the additive Haar measure conditioned to the box `adelicBox K`.
--
--   **The cuspidal system.** A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}_i\in$ `HeckeEigensystem K ℂ` indexed by $\iota$, subject to: `hb`, each $\mathrm{cls}_i$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing $a_v,b_v$ for $v\in S_K$, nonzero isotypic cuspidal submodule) and $b_i$ lies in `isotypicCuspSubmodule K pins ξK N SK (cls i) ⊓ archCutSubmodule K tysK`; `hbn`, $\int b_i\overline{b_i}=1$ over `canonicalTruncationDomain K α β` against the adelic Haar measure; `hbo`, the corresponding integrals $\int b_i\overline{b_j}$ vanish for $i\neq j$; `hbs`, for every class $\pi$ in `cuspClasses K pins ξK N SK` the fibre $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the complex span of its image under $b$ equals `isotypicCuspSubmodule K pins ξK N SK π ⊓ archCutSubmodule K tysK`; and `hbc`, the completeness statement that any $\varphi$ which is a smooth cuspidal automorphic function for `pins` and $\xi_K$, is continuous, is right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, lies in `archCutSubmodule K tysK`, and is orthogonal to every $b_i$ over the truncation domain, vanishes almost everywhere for the adelic Haar measure restricted to that domain.
--
--   **The Eisenstein frame.** A countable type $\iota_E$; families of characters $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$; natural numbers $n_E(e)$; and functions $\varphi_E(e,j):\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ for $j\in\mathrm{Fin}(n_E\,e)$. The hypotheses on these (summarised here by groups) are: unitarity of each $\mu_e,\nu_e$ (`_hμ`, `_hν`); triviality on $K^\times$, i.e. the idele-class condition (`_hμic`, `_hνic`); continuity (`_hμc`, `_hνc`); the central compatibility $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all ideles $z$ (`_hμν`); separation of distinct indices on the norm-one ideles, the kernel of the distributive Haar character (`_hdist`); and, for the sections, that each $\varphi_E(e,j,s)$ is an induced section for the pair $(\mathrm{etaFst}\,\mu_e\,s,\ \mathrm{etaSnd}\,\nu_e\,s)$ (`_hφE`), is archimedean $K$-finite (`_hφEK`) and $K_f$-smooth (`_hφEf`), is jointly continuous in $(s,g)$ (`_hφEjc`), is holomorphic in $s$ for fixed $g$ (`_hφEhol`), satisfies a uniform $K$-finiteness condition with one finite-dimensional space $W$ of functions on the row-isometry subgroup at each infinite place serving for all $s$ and $g$ (`_hφEKu`), is flat on the maximal compact subgroup, i.e. $\varphi_E(e,j,s,k)=\varphi_E(e,j,0,k)$ for $k$ in `adelicMaximalCompact K` (`_hφEflat`), is right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`), lies in `archCutSubmodule K tysK` for each $s$ (`_hφEty`), and is orthonormal on the maximal compact subgroup with respect to `maximalCompactHaar K` at $s=0$, the integral of $\varphi_E(e,i,0,k)\overline{\varphi_E(e,j,0,k)}$ being $1$ for $i=j$ and $0$ otherwise (`_hφEon`). Two further hypotheses describe the frame: `_hφEspan`, on the unitary axis $s=it$ every continuous, archimedean $K$-finite, level-invariant induced section for $(\mu_e,\nu_e)$ lying in `archCutSubmodule K tysK` belongs to the span of the $\varphi_E(e,j,it)$; and `_hpairs`, every pair $(\mu',\nu')$ of continuous unitary idele-class characters with $\mu'\nu'=\xi_K$ admitting a nonzero such section at some $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Finally, sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j),N_E(e,j):\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, with the hypothesis `_hEE` (a nine-clause conjunction) requiring that $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$, that $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$ for each $g$, that both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$ jointly, that for $\mathrm{Re}\,s>1/2$ one has $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E(e,j,s,\,w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix with upper entry the image of $\xi$, and that for $\mathrm{Re}\,s>1/2$ one has $N_E(e,j,s,g)=\int_{\mathbb{A}_K}\varphi_E(e,j,s,\,w^{-1}u(x)g)\,dx$ against the adelic additive Haar measure.
--
--   **The test function.** A function $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is continuous (`_hf`) with compact support (`_hfc`), factorizable in the sense of `IsFactorizableTestFn` (a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` in the sense of `IsBiInvariantUnder`, and archimedeanly bi-finite for $\mathrm{tys}_K$ in the sense of `IsArchBiFinite` ($g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`).
--
--   **The perturbation data.** A real $\varepsilon>0$ and four coefficient families $X_1,X_2,Y_1,Y_2$, each assigning to $e\in\iota_E$ and $j\in\mathrm{Fin}(n_E\,e)$ a function $\mathbb{R}\to\mathbb{C}$, subject to four hypotheses: each $Y_1(e,j)$ lies in $L^2(\mathbb{R})$ and $e\mapsto\int_{\mathbb{R}}\sum_j\lVert Y_1(e,j,t)\rVert^2\,dt$ is summable; the same for $Y_2$; each $X_1(e,j)-Y_1(e,j)$ lies in $L^2$, $e\mapsto\int\sum_j\lVert X_1(e,j,t)-Y_1(e,j,t)\rVert^2$ is summable, and $\sum_{e}\int\sum_j\lVert X_1(e,j,t)-Y_1(e,j,t)\rVert^2\le\varepsilon^2$; and likewise for $X_2-Y_2$. No square-integrability hypothesis is imposed on $X_1,X_2$ themselves.
--
--   **Conclusion.** Write $\mathrm{rightConv}\,\varphi\,f\,(g)=\int_{\mathrm{GL}_2(\mathbb{A}_K)}\varphi(gx)f(x)\,dx$ for the adelic Haar measure, and for $e\in\iota_E$, $i,j\in\mathrm{Fin}(n_E\,e)$ and $t\in\mathbb{R}$ put
--   $$a_{e,ij}(t)=\int_{\mathrm{adelicMaximalCompact}\,K}\bigl(\mathrm{rightConv}\,\varphi_E(e,j,it)\,f\bigr)(k)\;\overline{\varphi_E(e,i,it)(k)}\;d(\mathrm{maximalCompactHaar}\,K).$$
--   Then the following five assertions hold. First, for every $e$ the function $t\mapsto\sum_{i}\sum_{j}a_{e,ij}(t)\,\bigl(X_2(e,j,t)\overline{X_1(e,i,t)}\bigr)$ is integrable on $\mathbb{R}$. Second, $e\mapsto\int_{\mathbb{R}}\sum_{i}\sum_{j}a_{e,ij}(t)\,\bigl(X_2(e,j,t)\overline{X_1(e,i,t)}\bigr)\,dt$ is summable. Third, for every $e$ the function $t\mapsto\sum_{i}\sum_{j}a_{e,ij}(t)\,\bigl(Y_2(e,j,t)\overline{Y_1(e,i,t)}\bigr)$ is integrable. Fourth, $e\mapsto\int_{\mathbb{R}}\sum_{i}\sum_{j}a_{e,ij}(t)\,\bigl(Y_2(e,j,t)\overline{Y_1(e,i,t)}\bigr)\,dt$ is summable. Fifth, the difference of the two resulting sums is bounded by
--   $$\Bigl\lVert\sum_{e}\int_{\mathbb{R}}\sum_{i,j}a_{e,ij}(t)X_2(e,j,t)\overline{X_1(e,i,t)}\,dt-\sum_{e}\int_{\mathbb{R}}\sum_{i,j}a_{e,ij}(t)Y_2(e,j,t)\overline{Y_1(e,i,t)}\,dt\Bigr\rVert\le\Bigl(\int\lVert f\rVert\Bigr)\,\varepsilon\,\Bigl(\sqrt{\textstyle\sum_{e}\int\sum_j\lVert X_1(e,j,t)\rVert^2}+\sqrt{\textstyle\sum_{e}\int\sum_j\lVert X_2(e,j,t)\rVert^2}+\varepsilon\Bigr),$$
--   where $\int\lVert f\rVert$ is taken against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ and the sums over $e$ are the corresponding unconditional sums.
--
--   This is the stability, or boundedness, estimate for the bilinear form in the coefficient families that represents the continuous (Eisenstein) part of the spectral expansion of the convolution operator $R(f)$: the matrices $a_{e,ij}(t)$ are those of the operators $\pi_{it}(f)$ in the $\mathbf{K}$-orthonormal frame $\varphi_E(e,j,it)$, and the form they define is bounded by $\int\lVert f\rVert$ on the coefficient Hilbert space, so that replacing the coefficient families by $L^2$-approximations changes the value by at most the stated amount. It is used in the density step for the spectral identity [`AutomorphicForm.forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener`](thm.html#AutomorphicForm.forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener), where the continuous-spectrum contribution is first computed for Paley–Wiener coefficient data and then extended.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le.lean

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

theorem AutomorphicForm.norm_tsum_integral_sum_rightConv_mul_mul_conj_sub_le_of_tsum_integral_sum_normSq_sub_le
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
    ∀ (ε : ℝ) (_hε : 0 < ε)
      (X₁ X₂ Y₁ Y₂ : (e : ιE) → Fin (nE e) → ℝ → ℂ),
      ((∀ (e : ιE) (j : Fin (nE e)), MemLp (Y₁ e j) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖Y₁ e j t‖ ^ (2 : ℕ))) → ((∀ (e : ιE) (j : Fin (nE e)), MemLp (Y₂ e j) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖Y₂ e j t‖ ^ (2 : ℕ))) →
      ((∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => X₁ e j t - Y₁ e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₁ e j t - Y₁ e j t‖ ^ (2 : ℕ)) ∧
      ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₁ e j t - Y₁ e j t‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ)) → ((∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => X₂ e j t - Y₂ e j t) 2) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₂ e j t - Y₂ e j t‖ ^ (2 : ℕ)) ∧
      ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₂ e j t - Y₂ e j t‖ ^ (2 : ℕ) ≤ ε ^ (2 : ℕ)) →
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (X₂ e j t * conj (X₁ e i t)))) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (X₂ e j t * conj (X₁ e i t))) ∧
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (Y₂ e j t * conj (Y₁ e i t)))) ∧
      Summable (fun e : ιE => ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (Y₂ e j t * conj (Y₁ e i t))) ∧
      ‖(∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (X₂ e j t * conj (X₁ e i t))) -
          (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (Y₂ e j t * conj (Y₁ e i t)))‖ ≤
        (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ε * (Real.sqrt (∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₁ e j t‖ ^ (2 : ℕ)) + Real.sqrt (∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), ‖X₂ e j t‖ ^ (2 : ℕ)) + ε) := by sorry
