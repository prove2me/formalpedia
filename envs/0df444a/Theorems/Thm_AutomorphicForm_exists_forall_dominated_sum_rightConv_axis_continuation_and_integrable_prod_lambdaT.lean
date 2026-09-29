-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT
-- name    : AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1eb773db-bb43-54b2-a600-fd45418e8227
-- title:
--   Dominated and integrable continuous spectral kernel after truncation
-- statement:
--   Throughout, $\mathbb A$ denotes the adele ring of the number field $K$, $G=\mathrm{GL}_2(\mathbb A)$ (in Lean `AdelicGL2 (𝓞 K) K`), and $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the domain component of the truncation datum selected for the pair $(\alpha,\beta)$ by a classical choice (the empty set if no such datum exists).
--
--   **Parameters and geometric data.** Reals $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`); a set $\Phi_K\subseteq G$; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`), $d_{1K}<d_{2K}$ (`hdK`); a finite set $T_K\subseteq G$. The hypothesis `hcovK` asserts `CoversModCentre` for $\bigcup_{x\in T_K}(\cdot\, x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K`: every $g\in G$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ such that `globalPoints` $\gamma\cdot g\cdot$ `centralScalar` $z$ lies in that union, the centre-cut Siegel set consisting of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has local height $\ge c_K$ and $x$-window square $\le u_K^2$, and whose archimedean determinant norm at each infinite place lies in $[d_{1K},d_{2K}]$.
--
--   **Central data.** A measurable space and Borel structure on $\mathbb A^\times$, a Haar measure $\nu_{Z,K}$ on $\mathbb A^\times$, and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the range of $K^\times\to\mathbb A^\times$ with respect to $\nu_{Z,K}$.
--
--   **Character, level and type data.** A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the top subgroup of $\mathbb A^\times$ to $\mathbb C^\times$, which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N\subseteq\mathcal O_K$ with every place $v$ whose prime divides $N$ lying in $S_K$ (`hN`); and an `ArchTypeFamily` $\mathrm{tys}_K$, i.e. for each infinite place $w$ a finite list of representations of the row-isometry group at $w$. The modulus character $\alpha_m$ is the composite of `distribHaarChar` on $\mathbb A$ with $\mathbb R_{\ge0}\to\mathbb R$, viewed as a homomorphism into $\mathbb R^\times$, and `hαm` asserts that it takes strictly positive values.
--
--   Write $P$ for `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier pins whose measurable space on $G$ is the Borel one and whose measure is `adelicGLHaar`, whose domain is $\Phi_0$, whose central subgroup is all of $\mathbb A^\times$, whose level subgroups are $U(M)=$ `principalLevel (𝓞 K) K M` $\sqcap$ `finiteAdelicGL2Subgroup K`, whose Hecke generators are `heckeGen (𝓞 K) K v`, and whose data on $\mathbb A$ are the Borel σ-algebra together with the conditional measure of `adelicAddHaar` on `adelicBox K`.
--
--   **Cusp-basis data.** A type $\iota$, functions $b_i:G\to\mathbb C$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb C$ such that: (`hb`) each $\mathrm{cls}(i)$ is a cusp class for $P,\xi_K,N,S_K$ (level $N$, with $a_v=b_v=0$ for $v\in S_K$, and non-zero isotypic cusp submodule) and $b_i$ lies in the intersection of `isotypicCuspSubmodule` for $\mathrm{cls}(i)$ — the span of the functions that are smooth cuspidal automorphic for $P$ and $\xi_K$, continuous, invariant under right translation by $U(N)$, Hecke eigenfunctions with eigenvalue $a_v$ and central eigenvalue $b_v$ at all $v\notin S_K$ — with `archCutSubmodule K tysK`; (`hbn`, `hbo`) the $b_i$ are orthonormal for the integral over $\Phi_0$ against `adelicGLHaar`; (`hbs`) for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the complex span of the corresponding $b_i$ equals the isotypic cusp submodule of $\pi$ cut by the archimedean types; (`hbc`) completeness: any $\varphi$ which is smooth cuspidal automorphic for $P$ and $\xi_K$, continuous, invariant under right translation by $U(N)$, lies in `archCutSubmodule K tysK` and is orthogonal over $\Phi_0$ to every $b_i$, vanishes almost everywhere for `adelicGLHaar` restricted to $\Phi_0$.
--
--   **Eisenstein parameter data.** A countable type $\iota_E$ and families of characters $\mu_e,\nu_e:\mathbb A^\times\to\mathbb C^\times$ with: `_hμ`, `_hν` unitarity (all values of absolute value $1$); `_hμic`, `_hνic` triviality on the image of $K^\times$; `_hμc`, `_hνc` continuity; `_hμν` the identity $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $z$; `_hdist` separation: distinct $e\ne e'$ admit $z$ in [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16) (the kernel of `distribHaarChar`) with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$.
--
--   **Section families.** Integers $n_E(e)$ and functions $\varphi_{e,j}(s):G\to\mathbb C$ for $j\in\mathrm{Fin}(n_E(e))$, $s\in\mathbb C$, subject to the following hypotheses. `_hφE`: each $\varphi_{e,j}(s)$ is an induced section for the pair `etaFst (μ e) αm hαm s` $=\mu_e\cdot|\cdot|^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\cdot|\cdot|^{-(s+1/2)}$, the modulus being $\alpha_m$; that is, $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup. `_hφEK`: archimedean $K$-finiteness at every infinite place (the right translates under `archRowIsometrySubgroup` span a finite-dimensional space). `_hφEf`: smoothness as a vector for the finite-adelic subgroup. `_hφEjc`: joint continuity of $(s,g)\mapsto\varphi_{e,j}(s)(g)$. `_hφEhol`: complex differentiability of $s\mapsto\varphi_{e,j}(s)(g)$ for each $g$. `_hφEKu`: at each infinite place $w$ a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K w`, independent of $s$ and $g$, containing all functions $k\mapsto\varphi_{e,j}(s)(gk)$. `_hφEflat`: on the adelic maximal compact subgroup the value at $s$ agrees with the value at $s=0$. `_hφElev`: right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`. `_hφEty`: each $\varphi_{e,j}(s)$ lies in `archCutSubmodule K tysK`. `_hφEon`: the $\varphi_{e,j}(0)$ are orthonormal on the adelic maximal compact for `maximalCompactHaar K`. `_hφEspan`: for each $e$ and each real $t$, every induced section $\varphi_0$ for the pair at $s=it$ which is continuous, archimedean $K$-finite, right $N$-level invariant and of the prescribed archimedean types lies in the span of $\{\varphi_{e,j}(it)\}_j$. `_hpairs`: exhaustiveness of the parameter family — for every pair $(\mu',\nu')$ of continuous unitary characters trivial on $K^\times$ with $\mu'\nu'=\xi_K$, every real $t$ and every non-zero induced section $\varphi_0$ at $s=it$ with the same continuity, $K$-finiteness, level and type properties, there is $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   **Continuation data.** Sets $O_{e,j}\subseteq\mathbb C$ and families $E_{e,j}(s),\,N_{e,j}(s):G\to\mathbb C$, subject to `_hEE`, a conjunction of nine clauses: $O_{e,j}$ is open, preconnected, and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on neighbourhoods of the points of $O_{e,j}$; both $(s,g)\mapsto E_{e,j}(s)(g)$ and $(s,g)\mapsto N_{e,j}(s)(g)$ are continuous on $O_{e,j}\times G$; for $\mathrm{Re}\,s>1/2$ one has the Eisenstein expression $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum'_{\xi\in K}\varphi_{e,j}(s)(w\,u(\xi)\,g)$, with $w=$ `adelicWeyl` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$, and $N_{e,j}(s)(g)=$ `weylIntertwiningIntegral` of $\varphi_{e,j}(s)$ at $g$, namely $\int \varphi_{e,j}(s)(w^{-1}u(x)g)$ against `adelicAddHaar`.
--
--   **Test function.** A function $f:G\to\mathbb C$ which is continuous (`_hf`), compactly supported (`_hfc`), factorizable (`IsFactorizableTestFn K f`: $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ compactly supported and given by a $C^\infty$ function of the matrix entries in the mixed space, and $f_{\mathrm{fin}}$ locally constant with compact support), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for $\mathrm{tys}_K$ (both $g\mapsto f(g^{-1})$ in `archCutSubmodule K tysK` and $f$ in `archDualCutSubmodule K tysK`).
--
--   Put, for $e\in\iota_E$, $i,j\in\mathrm{Fin}(n_E(e))$ and $t\in\mathbb R$,
--   $$a_{e,ij}(t)=\int_{\mathbf K}\big(\mathrm{rightConv}(\varphi_{e,j}(it),f)\big)(k)\,\overline{\varphi_{e,i}(it)(k)}\;d\,\mathrm{maximalCompactHaar},$$
--   where $\mathbf K$ is `adelicMaximalCompact K` and $\mathrm{rightConv}(\varphi,f)(g)=\int_G\varphi(gx)f(x)\,d\,$`adelicGLHaar`.
--
--   **Conclusion.** The assertion is the conjunction of the following two statements.
--
--   (A) For every $x\in G$ and every compact $C\subseteq G$ there exists $D:\iota_E\to\mathbb R\to\mathbb R$ such that each $D_e$ is integrable on $\mathbb R$, the family $e\mapsto\int_{\mathbb R}D_e(t)\,dt$ is summable, and for all $e$, all $t\in\mathbb R$ and all $y\in C$,
--   $$\Big\|\sum_{i,j\in\mathrm{Fin}(n_E(e))}a_{e,ij}(t)\,\big(E_{e,i}(it)(x)\,\overline{E_{e,j}(it)(y)}\big)\Big\|\le D_e(t).$$
--
--   (B) There exists $R_0\in\mathbb R$ such that for every $R\ge R_0$ both of the following hold: first, for each $e$ the function
--   $$(t,x)\longmapsto\sum_{i,j}a_{e,ij}(t)\,\Big(E_{e,i}(it)(x)\,\overline{\big(\Lambda^{e^R}E_{e,j}(it)\big)(x)}\Big)$$
--   is integrable with respect to the product of Lebesgue measure on $\mathbb R$ with `adelicGLHaar` restricted to $\Phi_0$; and second, the family of integrals of the norms of these functions, over the same product measure, is summable in $e$. Here $\Lambda^{e^R}$ is [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) with threshold $\exp R$, with the unipotent embedding $t\mapsto$ [`AutomorphicForm.unipotentGL2 t`](def/AutomorphicForm_ConstantTerm.html#L17), with height function [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) (the product of the archimedean and finite heights), and with the measurable space and measure taken from the fields `nS` and `ν` of `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, namely the Borel σ-algebra on $\mathbb A$ and the conditional measure of `adelicAddHaar` on `adelicBox K`; thus $(\Lambda^T\phi)(g)=\phi(g)$ minus the value at $g$ of the indicator, on $\{g\mid T<\mathrm{adelicHeight}(g)\}$, of the constant term of $\phi$ along that unipotent with respect to that measure. The two fields of the pins used by the truncation do not depend on the set $\Phi_K$.
--
--   Note that in (A) the point $x$ is fixed before the dominating family is produced, and the domination is uniform in $y$ over the compact set $C$, whereas in (B) the Eisenstein factor and the truncated Eisenstein factor are evaluated at the same point of the truncation domain.
--
--   This is the absolute-convergence statement for the continuous (Eisenstein) part of the spectral side of the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over a number field: a locally uniform, summable $L^1$ domination of the spectral kernel along the unitary axis, together with integrability on $\mathbb R\times\Phi_0$ and summability of the $L^1$ norms after one-cusp truncation at height $e^R$. It is what licenses moving the constant-term integral, the truncation operator and the integration over the truncation domain inside the spectral sum and the integral over the axis in the truncated spectral identities that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT.lean

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

theorem AutomorphicForm.exists_forall_dominated_sum_rightConv_axis_continuation_and_integrable_prod_lambdaT
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
    (∀ (x : AdelicGL2 (𝓞 K) K) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ D : ιE → ℝ → ℝ, (∀ e, Integrable (D e)) ∧ (Summable fun e : ιE => ∫ t : ℝ, D e t) ∧
        ∀ (e : ιE) (t : ℝ), ∀ y ∈ C,
          ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
              (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
              (EE e i ((t : ℂ) * Complex.I) x * conj (EE e j ((t : ℂ) * Complex.I) y))‖ ≤ D e t) ∧
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
