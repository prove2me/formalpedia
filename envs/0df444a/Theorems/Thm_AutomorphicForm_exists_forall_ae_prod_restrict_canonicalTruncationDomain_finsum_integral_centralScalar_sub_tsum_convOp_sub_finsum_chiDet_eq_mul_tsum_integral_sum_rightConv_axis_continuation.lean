-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_ae_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_tsum_integral_sum_rightConv_axis_continuation
-- name    : AutomorphicForm.exists_forall_ae_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_tsum_integral_sum_rightConv_axis_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/921c9d39-48be-54c1-a2ef-bc08e6596a14
-- title:
--   Almost-everywhere spectral expansion of the continuous kernel for GL₂
-- statement:
--   Global data. Let $K$ be a number field, and let $\alpha,\beta$ be real numbers with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`). A set $\Phi_K$ of elements of $\mathrm{GL}_2(\mathbb{A}_K)$ is among the arguments; it occurs in no hypothesis and in no part of the conclusion. Real numbers $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ are given with $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`), $d_{1K}<d_{2K}$ (`hdK`), and the covering hypothesis `hcovK`: the union $\bigcup_{x\in T_K}\,(\cdot\,x)''\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ satisfies `CoversModCentre`, i.e. for every $g\in \mathrm{GL}_2(\mathbb{A}_K)$ there are $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\mathrm{globalPoints}(\gamma)\cdot g\cdot \mathrm{centralScalar}(z)$ in that union; here the centre-cut Siegel set consists of the $g$ whose finite part is integral, whose archimedean components at every infinite place have local height at least $c_K$ and window square at most $u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$.
--
--   The idele class group carries a measurable structure with the Borel property, a Haar measure $\nu_{Z,K}$, and a set $\Omega_K$ which by `hΩK` is a fundamental domain, with respect to $\nu_{Z,K}$, for the range of $K^\times\to \mathbb{A}_K^\times$ acting on the ideles. Further data: a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup of ideles to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the principal ideles (`hξt`), and of absolute value $1$ everywhere (`hξu`); an ideal $N$ of $\mathcal{O}_K$ such that every finite place whose prime divides $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, that is, a cardinality function on the infinite places together with, at each infinite place $w$, that many finite-dimensional representations of the row-isometry group of $K_w$.
--
--   Write $\alpha_m$ for the homomorphism from the ideles to $\mathbb{R}^\times$ obtained from the module character $\mathrm{distribHaarChar}(\mathbb{A}_K)$ followed by $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume `hαm`, that $\alpha_m$ takes strictly positive values. The adele ring is given its Borel measurable structure.
--
--   The assertion is the existence of a real $\kappa>0$ — chosen before all the data below, hence uniform in the cuspidal system, the Eisenstein system and the test function — such that the following holds.
--
--   The cuspidal system. For every type $\iota$, every family $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and every assignment $\mathrm{cls}:\iota\to$ Hecke eigensystems over $\mathbb{C}$ (a level ideal, nonzero, and coefficient functions $a,b$ on finite places) subject to: `hb`, each $\mathrm{cls}\,i$ lies in $\mathrm{cuspClasses}$ for the carrier pins $\mathrm{productionPinsOf}$ built from the canonical truncation domain $\Phi_0=\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$, the level subgroups $M\mapsto \mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$ and the adelic box (so: level $N$, vanishing coefficients at the places of $S_K$, and nonzero isotypic cuspidal subspace), and $b\,i$ lies in the intersection of the isotypic cuspidal submodule of $\mathrm{cls}\,i$ with the submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$ cut out by the archimedean types; `hbn`, $\int_{\Phi_0} b\,i\cdot\overline{b\,i}=1$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$; `hbo`, $\int_{\Phi_0} b\,i\cdot\overline{b\,j}=0$ for $i\neq j$; `hbs`, for each cuspidal class $\pi$ the set $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b\,i$ is exactly the isotypic cuspidal submodule of $\pi$ intersected with the archimedean cut submodule; and `hbc`, the completeness condition that any $\varphi$ which is a smooth cuspidal automorphic function for these pins and $\xi_K$, continuous, invariant under right translation by the level subgroup attached to $N$, lying in the archimedean cut submodule, and orthogonal on $\Phi_0$ to every $b\,i$, vanishes almost everywhere for the Haar measure restricted to $\Phi_0$.
--
--   The Eisenstein system. For every countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ subject to: unitarity of each $\mu_e$ and $\nu_e$ (`_hμ`, `_hν`), triviality on $K^\times$ (`_hμic`, `_hνic`), continuity (`_hμc`, `_hνc`), the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $z$ (`_hμν`), and separation: for $e\neq e'$ some norm-one idele distinguishes $\mu_e$ from $\mu_{e'}$ or $\nu_e$ from $\nu_{e'}$ (`_hdist`). For every $n_E:\iota_E\to\mathbb{N}$ and every family $\varphi_{E}$ assigning to $e$, $j<n_E(e)$ and $s\in\mathbb{C}$ a function on $\mathrm{GL}_2(\mathbb{A}_K)$, subject to the following hypotheses, each holding for all $e,j$ and all $s$ where relevant: `_hφE`, $\varphi_E(e,j,s)$ is an induced section for the pair $\eta_1=\mu_e\cdot\alpha_m^{\,s+1/2}$, $\eta_2=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK`, archimedean $K$-finiteness at every infinite place; `_hφEf`, smoothness for the finite-adelic subgroup; `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, at each infinite place $w$ a finite-dimensional subspace of functions on the archimedean row-isometry subgroup containing all the functions $k\mapsto \varphi_E(e,j,s)(gk)$; `_hφEflat`, $\varphi_E(e,j,s)(k)=\varphi_E(e,j,0)(k)$ for $k$ in the adelic maximal compact subgroup; `_hφElev`, right invariance under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$; `_hφEty`, membership in the archimedean cut submodule; `_hφEon`, orthonormality of the $\varphi_E(e,\cdot,0)$ on the maximal compact subgroup for its Haar measure; `_hφEspan`, for each $e$ and each real $t$, every continuous, archimedean $K$-finite, level-$N$-invariant section in the archimedean cut submodule induced from the characters at $s=it$ lies in the span of the $\varphi_E(e,j,it)$; and `_hpairs`, the exhaustiveness condition that any pair $(\mu',\nu')$ of continuous unitary characters trivial on $K^\times$ with $\mu'\nu'=\xi_K$ admitting a nonzero such section at some point $it$ of the axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Finally, for families of subsets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j,\cdot,\cdot)$, $N_E(e,j,\cdot,\cdot)$ subject to `_hEE`: each $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times \mathrm{GL}_2(\mathbb{A}_K)$ as functions of $(s,g)$; for $\operatorname{Re}s>1/2$ one has the Eisenstein series expansion $E_E(e,j,s,g)=\varphi_E(e,j,s)(g)+\sum'_{\,\xi\in K}\varphi_E(e,j,s)(w\cdot u(\xi)\cdot g)$ with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent matrix; and for $\operatorname{Re}s>1/2$, $N_E(e,j,s,g)$ equals the Weyl intertwining integral $\int \varphi_E(e,j,s)(w^{-1}u(x)g)\,dx$ for the additive adelic Haar measure. (The functions $N_E$ enter only through `_hEE`.)
--
--   The test function. For every $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ that is continuous (`_hf`) with compact support (`_hfc`), and that is factorizable, that is $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ compactly supported and given by a smooth function of the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant with compact support; bi-invariant under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, i.e. $f(ug)=f(g)=f(gu)$ for all $u$ in that subgroup and all $g$; and archimedean bi-finite for $\mathrm{tys}_K$, i.e. $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ lies in the archimedean dual cut submodule.
--
--   Conclusion. Writing $V$ for the real number $\nu_{Z,K}\bigl(\Omega_K\cap\{z\mid \mathrm{ideleNorm}(\det \mathrm{centralScalar}(z))\in[\alpha,\beta]\}\bigr)$, viewed in $\mathbb{C}$, and $V_0$ for the corresponding real volume of $\Phi_0$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the following identity holds for almost every pair $p=(p_1,p_2)$ with respect to the product of two copies of the adelic Haar measure restricted to $\Phi_0$:
--   $$\Bigl(\sum^{\mathrm{f}}_{q\in \mathrm{GL}_2(K)/Z}\int \xi_K(z)\, f\bigl(p_1^{-1}\,\mathrm{globalPoints}(\tilde q)\,(\mathrm{centralScalar}(z)\,p_2)\bigr)\,d\nu_{Z,K}(z)\Bigr) - V\sum_{i\in\iota}' \bigl(\mathrm{convOp}\,f\,(b\,i)\bigr)(p_1)\,\overline{b\,i(p_2)}$$
--   $$-\ \frac{V}{V_0}\ \sum^{\mathrm{f}}_{\chi}\Bigl(\int f\cdot \chi\circ\det\Bigr)\bigl(\chi(\det p_1)\,\chi^{-1}(\det p_2)\bigr)\ =\ \kappa \sum_{e\in\iota_E}' \int_{\mathbb{R}} \sum_{i,j<n_E(e)} a_{e,ij}(t)\, E_E(e,i,it,p_1)\,\overline{E_E(e,j,it,p_2)}\,dt .$$
--   Here the first term is the finsum over the quotient of $\mathrm{GL}_2(K)$ by its centre, evaluated at the chosen representative $\tilde q$ of each class; the second sum is over $\iota$, with $\mathrm{convOp}\,f\,u=\mathrm{rightConv}\,u\,f$, namely $g\mapsto \int u(gx)f(x)\,dx$ for the adelic Haar measure; the third is the finsum over those characters $\chi$ of the ideles that square to $\xi_K$ on all of $\mathbb{A}_K^\times$, are trivial on the principal ideles and are continuous, with $\chi\circ\det$ denoting $\mathrm{chiDet}$; and on the right $a_{e,ij}(t)=\int \bigl(\mathrm{rightConv}\,(\varphi_E(e,j,it))\,f\bigr)(k)\,\overline{\varphi_E(e,i,it)(k)}\,dk$ over the adelic maximal compact subgroup for its Haar measure, the $t$-integral being over $\mathbb{R}$ and the outer sum over $\iota_E$.
--
--   This is the $L^2$ form of the spectral decomposition of the continuous part of the folded kernel for $\mathrm{GL}_2$ over a number field: the centre-folded kernel of $R(f)$, with its cuspidal and residual (determinant-twist) blocks removed, is expanded almost everywhere on $\Phi_0\times\Phi_0$ along the unitary axis in terms of Eisenstein series attached to the pairs $(\mu_e,\nu_e)$. It is the measure-theoretic input to the pointwise version of the expansion, which combines it with the joint continuity and automorphy of the four kernels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_ae_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_tsum_integral_sum_rightConv_axis_continuation.lean

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

theorem AutomorphicForm.exists_forall_ae_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_tsum_integral_sum_rightConv_axis_continuation
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
    ∀ᵐ p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        (AutomorphicForm.canonicalTruncationDomain K α β)).prod
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))),
      (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * p.2)) ∂νZK) -
        (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) p.1 * conj (b i p.2)) -
        (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ p.1 * chiDet (𝓞 K) K χ⁻¹ p.2)) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) p.1 * conj (EE e j ((t : ℂ) * Complex.I) p.2)) := by sorry
