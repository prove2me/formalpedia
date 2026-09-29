-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2cf98a1e-9b58-5956-8900-658e3774e95b
-- title:
--   Integrability of the truncated continuous kernel, summably in the Eisenstein data
-- statement:
--   Throughout, $K$ is a number field, and $\alpha,\beta$ are reals with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`). Write $G=$ `AdelicGL2 (𝓞 K) K` $=\mathrm{GL}_2$ of the adele ring of $K$, and let `adelicGLHaar (Fin 2) (𝓞 K) K` be the Haar measure on $G$ for the Borel $\sigma$-algebra `glBorel`.
--
--   **Siegel covering data.** A set $\Phi_K\subseteq G$ is given, together with reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq G$, subject to $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`), $d_{1K}<d_{2K}$ (`hdK`) and `hcovK`: the union $\bigcup_{x\in T_K}(\,\cdot\,x)$-translates of `centreCutSiegelSet K cK uK d₁K d₂K` covers $G$ modulo the centre, i.e. for every $g\in G$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,z$ in that union (where `centreCutSiegelSet` consists of the $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c_K$, whose window squares are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$).
--
--   **Centre data.** The idele unit group $(\mathbb A_K)^\times$ carries a measurable and Borel structure, $\nu_{ZK}$ is a Haar measure on it, and $\Omega_K$ is a fundamental domain for the image of $K^\times$ (the range of `Units.map (algebraMap K (AdeleRing (𝓞 K) K))`) acting on $(\mathbb A_K)^\times$ with respect to $\nu_{ZK}$ (`hΩK`).
--
--   **Central character, level and archimedean types.** $S_K$ is a finite set of finite places; $\xi_K$ is a monoid homomorphism from the full subgroup $\top$ of $(\mathbb A_K)^\times$ to $\mathbb C^\times$, continuous as a $\mathbb C$-valued function (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`). $N$ is an ideal of $\mathcal O_K$ such that every place dividing $N$ lies in $S_K$ (`hN`), and `tysK : ArchTypeFamily K` prescribes, at each infinite place $w$, a finite list of representations of the local row-isometry group; `archCutSubmodule K tysK` is the intersection over $w$ of the sums of the corresponding type submodules.
--
--   The statement then introduces $\alpha_m$, the homomorphism $(\mathbb A_K)^\times\to\mathbb R^\times$ obtained from the module character `distribHaarChar (AdeleRing (𝓞 K) K)` through $\mathbb R_{\ge 0}\to\mathbb R$, equips the adele ring with `adeleBorel`, and quantifies over the hypothesis `hαm` that all values $\alpha_m(x)$ are positive.
--
--   All automorphic notions are taken with respect to the carrier data `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: Borel $\sigma$-algebra and Haar measure on $G$, domain the canonical truncation domain [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) attached to the determinant slab $[\alpha,\beta]$, central subgroup $\top$, level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators `heckeGen (𝓞 K) K v`, and, on the adele ring, the Borel $\sigma$-algebra together with the conditioning of `adelicAddHaar (𝓞 K) K` on `adelicBox K`.
--
--   **Cuspidal basis data.** An index type $\iota$, functions $b:\iota\to(G\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` are given with: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses` for these pins, $\xi_K$, $N$, $S_K$ (level $N$, vanishing Hecke and central data at the places of $S_K$, non-zero isotypic space) and $b\,i$ lies in the intersection of `isotypicCuspSubmodule` for $\mathrm{cls}\,i$ with `archCutSubmodule K tysK`; `hbn`, each $b\,i$ has $\int b\,i\cdot\overline{b\,i}=1$ over the canonical truncation domain against `adelicGLHaar`; `hbo`, the corresponding integrals for $i\neq j$ vanish; `hbs`, for every class $\pi$ in `cuspClasses` the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb C$-span of its $b$-values is exactly the intersection of the $\pi$-isotypic cusp submodule with `archCutSubmodule K tysK`; and `hbc`, completeness: any $\varphi:G\to\mathbb C$ which is a smooth cuspidal automorphic function for these pins and $\xi_K$, is continuous, is right invariant under $U(N)$, lies in `archCutSubmodule K tysK`, and is orthogonal to every $b\,i$ over the canonical truncation domain, vanishes almost everywhere for `adelicGLHaar` restricted to that domain.
--
--   **Eisenstein data.** A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to((\mathbb A_K)^\times\to\mathbb C^\times)$ are given, subject to: unitarity of each $\mu_e$, $\nu_e$ (`_hμ`, `_hν`); triviality on $K^\times$, i.e. the idele-class condition (`_hμic`, `_hνic`); continuity (`_hμc`, `_hνc`); the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $z$ (`_hμν`); and separation (`_hdist`): distinct $e,e'$ are distinguished by some norm-one idele, on which $\mu$ or $\nu$ differ.
--
--   Further, integers $n_E(e)$ and functions $\varphi_E(e,j,s,\cdot)$ are given for $j\in\mathrm{Fin}(n_E(e))$ and $s\in\mathbb C$, with the following hypotheses: each $\varphi_E(e,j,s,\cdot)$ is an induced section for the pair of characters `etaFst (μ e) αm hαm s`, `etaSnd (ν e) αm hαm s`, i.e. transforms under left multiplication by the adelic Borel by the product of these characters evaluated on the two diagonal entries (`_hφE`); it is archimedean $K$-finite (`_hφEK`) and $K_f$-smooth (`_hφEf`); it is jointly continuous in $(s,g)$ (`_hφEjc`) and holomorphic in $s$ for each $g$ (`_hφEhol`); at each infinite place $w$ the right translates along `archRowIsometrySubgroup K w` lie in one fixed finite-dimensional subspace, uniformly in $s$ and $g$ (`_hφEKu`); the restriction to the maximal compact subgroup is independent of $s$ (`_hφEflat`); it is right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`) and lies in `archCutSubmodule K tysK` (`_hφEty`); the restrictions to `adelicMaximalCompact K` at $s=0$ are orthonormal for `maximalCompactHaar K` (`_hφEon`); and, for every $e$ and every real $t$, every induced section $\varphi_0$ for the characters at $s=it$ which is continuous, archimedean $K$-finite, right invariant under the level group and of the prescribed archimedean types lies in the $\mathbb C$-span of the $\varphi_E(e,j,it,\cdot)$ (`_hφEspan`). The hypothesis `_hpairs` asserts exhaustiveness of the families $\mu,\nu$: for every pair of characters $\mu',\nu'$ that are unitary, idele-class, continuous and satisfy $\mu'\nu'=\xi_K$, and every real $t$ and every non-zero $\varphi_0$ satisfying the same section, continuity, $K$-finiteness, level and type conditions at $s=it$, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   Finally, sets $O_E(e,j)\subseteq\mathbb C$ and families $E_E(e,j,s,\cdot)$, $N_E(e,j,s,\cdot)$ are given, and `_hEE` collects for each $(e,j)$ the nine clauses: $O_E(e,j)$ is open, preconnected, contains the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ both $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times G$ as functions of $(s,g)$; for $\operatorname{Re}s>1/2$ one has the Eisenstein expansion $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}^{\prime}\varphi_E\bigl(e,j,s,\,w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl (𝓞 K) K` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$; and, in the same range, $N_E(e,j,s,g)$ equals the Weyl intertwining integral `weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g`.
--
--   **Test function.** $f:G\to\mathbb C$ is continuous (`_hf`) with compact support (`_hfc`), is a factorizable test function in the sense of `IsFactorizableTestFn K` (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), is bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and satisfies `IsArchBiFinite K tysK f`.
--
--   **Conclusion.** There exists $R_0\in\mathbb R$ such that for every real $R\ge R_0$ both of the following hold, where for $p=(t,x)\in\mathbb R\times G$ the kernel is
--   $$\Sigma_{e,R}(p)=\sum_{i,j}\Bigl(\int_{K_{\mathrm{max}}}\bigl(\mathrm{rightConv}\;\varphi_E(e,j,it,\cdot)\,f\bigr)(k)\,\overline{\varphi_E(e,i,it,k)}\,d\,\mathrm{maximalCompactHaar}\Bigr)\cdot\Bigl(E_E(e,i,it,x)\cdot\overline{\bigl(\Lambda^{e^R}E_E(e,j,it,\cdot)\bigr)(x)}\Bigr),$$
--   the sums being over $i,j\in\mathrm{Fin}(n_E(e))$, $K_{\mathrm{max}}=$ `adelicMaximalCompact K`, `rightConv K φ f g` $=\int_G\varphi(gx)f(x)$ against `adelicGLHaar`, and $\Lambda^{e^R}$ the truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with the adelic $\sigma$-algebra and measure components of `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)` (namely `adeleBorel` and the conditioning of `adelicAddHaar` on `adelicBox K`, the set $\Phi_K$ entering only through this carrier datum), with unipotent family $t\mapsto$ [`AutomorphicForm.unipotentGL2 t`](def/AutomorphicForm_ConstantTerm.html#L17), height function [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and threshold $\exp R$; thus $\Lambda^{e^R}\psi=\psi$ minus the indicator of $\{g:\exp R<\mathrm{ht}(g)\}$ times the constant term of $\psi$.
--
--   First, for every $e\in\iota_E$ the function $p\mapsto\Sigma_{e,R}(p)$ is integrable on $\mathbb R\times G$ for the product of Lebesgue measure on $\mathbb R$ with `adelicGLHaar (Fin 2) (𝓞 K) K` restricted to [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32).
--
--   Second, the family of integrals $e\mapsto\int_{\mathbb R\times G}\lVert\Sigma_{e,R}(p)\rVert$, with respect to the same product measure, is summable over $\iota_E$.
--
--   This is the integrability and summability step for the continuous (Eisenstein) part of the spectral expansion of a convolution kernel on $\mathrm{GL}_2$ over a number field: it supplies the Fubini–Tonelli licence for integrating the truncated kernel $\sum_{i,j}a_{e,ij}(t)E_{e,i,it}\overline{\Lambda^{R}E_{e,j,it}}$ over the imaginary axis and the truncation domain, term by term and summably over the Eisenstein data. It is used by [`AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT`](thm.html#AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain.lean

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

theorem AutomorphicForm.exists_forall_integrable_sum_rightConv_axis_continuation_mul_conj_lambdaT_prod_restrict_canonicalTruncationDomain
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
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ e : ιE, Integrable (fun p : ℝ × AdelicGL2 (𝓞 K) K => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((p.1 : ℂ) * Complex.I))) p.2)))
          ((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))) ∧
      (Summable fun e : ιE => ∫ p : ℝ × AdelicGL2 (𝓞 K) K, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((p.1 : ℂ) * Complex.I))) p.2))‖
          ∂((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))) := by sorry
