-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow
-- name    : AutomorphicForm.continuous_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/468eb79a-fb75-5110-bdef-652934c43168
-- title:
--   Continuity and polynomial growth of Eisenstein coefficients of θ_Ψ
-- statement:
--   Throughout, $K$ is a number field, and $\mathrm{GL}_2(\mathbb{A}_K)$ denotes `AdelicGL2 (𝓞 K) K`, the general linear group of degree $2$ over the adele ring of $K$, carrying its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`. Two reals $\alpha,\beta$ are given with $0<\alpha$ and $\alpha<\beta$, and $D :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the set of adelic matrices picked out as the last component of the classically chosen truncation datum for $(\alpha,\beta)$ (empty if no datum exists).
--
--   *Siegel covering data.* A set $\Phi_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ is given, which occurs in no further hypothesis and not in the conclusion. Reals $c_K,u_K,d_{1K},d_{2K}$ are given with $0<c_K$, $0<d_{1K}$ and $d_{1K}<d_{2K}$, together with a finite set $T_K$ of adelic matrices, and the hypothesis `hcovK` says that the union $\bigcup_{x\in T_K}\{g x : g \in \mathrm{centreCutSiegelSet}\}$ of right translates of the centre-cut Siegel set with parameters $c_K,u_K,d_{1K},d_{2K}$ (those $g$ whose finite part lies in `finiteIntegralGL2`, whose local height at every infinite place is at least $c_K$, whose window quantity `xWindowSq` at every infinite place is at most $u_K^2$, and whose archimedean determinant norm at every infinite place lies in $[d_{1K},d_{2K}]$) satisfies `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ (the image of $\gamma$ times $g$ times the central scalar matrix of $z$) in that union.
--
--   *Central data.* The idele group $\mathbb{A}_K^\times$ is equipped with a measurable and Borel structure, $\nu_{ZK}$ is a Haar measure on it, and $\Omega_K$ is a fundamental domain (`hΩK`) for the range of the principal-idele map $K^\times\to\mathbb{A}_K^\times$ acting on $\mathbb{A}_K^\times$ with respect to $\nu_{ZK}$. Further, $S_K$ is a finite set of finite places of $K$, and $\xi_K$ is a homomorphism from the full subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`). An ideal $N\subseteq\mathcal{O}_K$ is given with every place dividing $N$ belonging to $S_K$ (`hN`), and $\mathrm{tys}_K$ is an archimedean type family, i.e. for each infinite place $w$ a finite list of representations of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$; `archCutSubmodule K tysK` is the intersection over $w$ of the sums of the corresponding type submodules.
--
--   The character $\alpha_m : \mathbb{A}_K^\times \to \mathbb{R}^\times$ is defined as the unit-valued form of the composition of the module character `distribHaarChar (AdeleRing (𝓞 K) K)` with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and the adele ring is given its Borel structure. The assertion is then universally quantified over the hypothesis $\mathrm{h}\alpha_m$ that $\alpha_m(x)>0$ for all $x$, and over all of the following data.
--
--   *The cuspidal orthonormal family.* Write $P$ for the carrier pins `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, i.e. the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, domain $D$, central subgroup $\top$, level subgroups $M\mapsto \mathrm{principalLevel}(M)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}(v)$, and, on the adele ring, its additive Haar measure conditioned on the box `adelicBox K`. Given are an index type $\iota$, functions $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls} : \iota\to$ `HeckeEigensystem K ℂ`, subject to: `hb`, that for each $i$ the eigensystem $\mathrm{cls}(i)$ lies in `cuspClasses K P ξK N SK` (level $N$, vanishing $a_v,b_v$ for $v\in S_K$, and non-zero isotypic submodule) and $b(i)$ lies in the intersection of `isotypicCuspSubmodule K P ξK N SK (cls i)` (the span of the functions that are smooth cuspidal automorphic at $P$ with character $\xi_K$, continuous, right invariant under $P.U\,N$, Hecke eigenfunctions with eigenvalue $a_v$ and central eigenvalue $b_v$ outside $S_K$) with `archCutSubmodule K tysK`; `hbn`, that $\int_D b(i)\overline{b(i)}=1$; `hbo`, that $\int_D b(i)\overline{b(j)}=0$ for $i\ne j$; `hbs`, that for every $\pi$ in `cuspClasses K P ξK N SK` the fibre $\{i : \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ equals the intersection of the $\pi$-isotypic cuspidal submodule with the archimedean cut submodule; and `hbc`, completeness: every $\varphi$ that is smooth cuspidal automorphic at $P$ with character $\xi_K$, continuous, invariant under right translation by $P.U\,N$, a member of the archimedean cut submodule and orthogonal to every $b(i)$ over $D$, vanishes almost everywhere for the Haar measure restricted to $D$.
--
--   *The family of character pairs and induced sections.* Given are a countable type $\iota_E$ and families $\mu,\nu : \iota_E \to (\mathbb{A}_K^\times \to \mathbb{C}^\times)$ with: each $\mu_e,\nu_e$ of absolute value $1$ (`_hμ`, `_hν`), trivial on principal ideles (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), satisfying $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $z$ (`_hμν`), and pairwise separated on norm-one ideles: for $e\ne e'$ there is $z$ in the kernel of the module character with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$ (`_hdist`). Given further are $n_E : \iota_E\to\mathbb{N}$ and sections $\varphi_{e,j}(s,g)$ for $j\in\mathrm{Fin}(n_E\,e)$, subject to the following twelve hypotheses: each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair $\bigl(\mu_e\cdot\alpha_m^{\,s+1/2},\ \nu_e\cdot\alpha_m^{-(s+1/2)}\bigr)$, i.e. transforms by the product of these characters evaluated at the two diagonal entries under left translation by the adelic Borel subgroup (`_hφE`); is archimedean $K$-finite (`_hφEK`) and smooth for the finite adelic subgroup (`_hφEf`); is jointly continuous in $(s,g)$ (`_hφEjc`) and entire in $s$ for each $g$ (`_hφEhol`); satisfies uniform $K$-finiteness at each infinite place $w$, namely there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K w` containing all the right-translate functions $k\mapsto\varphi_{e,j}(s,gk)$ (`_hφEKu`); is flat on the maximal compact subgroup, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in `adelicMaximalCompact K` (`_hφEflat`); is right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`); lies in the archimedean cut submodule (`_hφEty`); and is orthonormal on the maximal compact subgroup, $\int \varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,d\,$`maximalCompactHaar`$=\delta_{ij}$ (`_hφEon`). Two further hypotheses complete the frame: `_hφEspan`, that for every $e$, every real $t$ and every $\varphi_0$ which is an induced section for the pair at $s=it$, continuous, archimedean $K$-finite, right invariant under that level subgroup and in the archimedean cut submodule, $\varphi_0$ lies in the span of the $\varphi_{e,j}(it,\cdot)$; and `_hpairs`, exhaustiveness, that for every pair of characters $\mu',\nu'$ of absolute value $1$, trivial on principal ideles, continuous and with product $\xi_K$, and every real $t$ and non-zero $\varphi_0$ satisfying the same five conditions at $s=it$, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   *The continuations.* Given are sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j} : \mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ such that, for all $e,j$ (`_hEE`, nine clauses): $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both $(s,g)\mapsto E_{e,j}(s,g)$ and $(s,g)\mapsto N_{e,j}(s,g)$ are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s>1/2$ one has the Bruhat expansion $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}\bigl(s,\ w\,u(\xi)\,g\bigr)$, with $w=$ `adelicWeyl` the image of the Weyl element and $u(\xi)$ the upper unipotent matrix with entry the principal adele of $\xi$; and for $\mathrm{Re}\,s>1/2$ one has $N_{e,j}(s,g)=\int_{\mathbb{A}_K}\varphi_{e,j}(s,\ w^{-1}u(x)g)\,dx$ for the additive adelic Haar measure.
--
--   *The test function and the indices.* Finally, $\Psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ is measurable (`_hΨm`), vanishes outside some compact set (`_hΨc`) and is bounded (`_hΨb`), and $e\in\iota_E$, $j\in\mathrm{Fin}(n_E\,e)$ are given.
--
--   Write $\theta_\Psi$ for the automorphised function
--   $$\theta_\Psi(g)\ =\ \sum^{\mathrm{f}}_{q\,\in\,\mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}\ \int_{\mathbb{A}_K^\times} \xi_K(w)^{-1}\,\bigl(\mathbf{1}_D\Psi\bigr)\bigl(\mathrm{centralScalar}(w)\cdot(\mathrm{globalPoints}(q.\mathrm{out})\cdot g)\bigr)\,d\nu_{ZK}(w),$$
--   the outer sum being the finite-support sum over the quotient of $\mathrm{GL}_2(K)$ by its centre, taken at chosen representatives, and $\mathbf 1_D\Psi$ the indicator of $D$ applied to $\Psi$.
--
--   The conclusion is a conjunction of two assertions about the coefficient integrals along the unitary axis $s=it$:
--
--   First, the function $t\mapsto \int_D \theta_\Psi(g)\,\overline{E_{e,j}\bigl((t:\mathbb{C})\cdot i,\ g\bigr)}\,d\,$`adelicGLHaar` is continuous on $\mathbb{R}$.
--
--   Second, there exist a real $A$ and a natural number $k$ such that for every $t\in\mathbb{R}$
--   $$\Bigl\|\int_D \theta_\Psi(g)\,\overline{E_{e,j}\bigl((t:\mathbb{C})\cdot i,\ g\bigr)}\,d\,\mathrm{adelicGLHaar}\Bigr\|\ \le\ A\,(1+|t|)^k .$$
--
--   The two conclusions are the regularity input — continuity in the spectral parameter and polynomial growth along the unitary axis — for the Eisenstein coefficients of the $\xi_K$-twisted central automorphisation $\theta_\Psi$ of a bounded, compactly supported test function against the continued Bruhat–Eisenstein series $E_{e,j}(it)$. It is used in the proof of [`AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq`](thm.html#AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq), the Bessel-type inequality for these coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow.lean

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

theorem AutomorphicForm.continuous_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow
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
      (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
      (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
      (_hΨb : ∃ M : ℝ, ∀ y, ‖Ψ y‖ ≤ M)
      (e : ιE) (j : Fin (nE e)),
    (Continuous fun t : ℝ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    ∃ (A : ℝ) (k : ℕ), ∀ t : ℝ, ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ k := by sorry
