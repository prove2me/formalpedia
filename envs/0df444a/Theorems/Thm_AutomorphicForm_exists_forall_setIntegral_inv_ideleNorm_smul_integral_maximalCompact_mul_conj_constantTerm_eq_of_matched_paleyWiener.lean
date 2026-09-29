-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/6e3b8148-c51f-50f3-ba7f-20a5e2c7975f
-- title:
--   Torus pairing of matched Paley–Wiener profile with Eisenstein constant terms
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal O_K$, and $\mathbb A_K$, $\mathbb A_K^\times$ denote its adele ring and idele group; $G:=\mathrm{GL}_2(\mathbb A_K)$ is `AdelicGL2 (𝓞 K) K`, equipped with its Borel $\sigma$-algebra and Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, and `diagOne y` is the matrix $\mathrm{diag}(y,1)$.
--
--   **Frame data.** Real numbers $\alpha,\beta$ with $0<\alpha<\beta$ are fixed, together with a set $\Phi_K\subseteq G$ to which no hypothesis is attached, real numbers $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$ and $0<d_{1K}<d_{2K}$, and a finite set $T_K\subseteq G$. The hypothesis `hcovK` states that the union $\bigcup_{x\in T_K}\{g\,x : g\in \mathrm{centreCutSiegelSet}\}$ of right translates of the centre-cut Siegel set of parameters $(c_K,u_K,d_{1K},d_{2K})$ — the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place $w$ has local height $\ge c_K$ and window $\mathrm{xWindowSq}\le u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$ — satisfies `CoversModCentre`: every $g\in G$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\,g\,z$ (the central scalar $z$ acting on the right) in that union.
--
--   Further: a finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the full idele group (presented as the subgroup $\top$) to $\mathbb C^\times$, continuous as a $\mathbb C$-valued function (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N\subseteq\mathcal O_K$ such that every prime dividing $N$ lies in $S_K$ (`hN`); and an `ArchTypeFamily` $\mathrm{tys}_K$, that is, for each infinite place $w$ a finite list of representations of the row-isometry group at $w$, whose associated type submodules cut out $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K=\bigcap_w\bigsqcup_i$ (type submodule).
--
--   The homomorphism $\alpha_m:\mathbb A_K^\times\to\mathbb R^\times$ is the one induced by the module character `distribHaarChar` of $\mathbb A_K$ composed with $\mathbb R_{\ge0}\to\mathbb R$, i.e. the idele norm viewed as a unit-valued character.
--
--   **Quantified measure-theoretic data.** The statement then quantifies over: a proof `hαm` that $\alpha_m$ takes positive values; a measurable set $D\subseteq\mathbb A_K^\times$ which is a fundamental domain for the subgroup [`M4aHerbrand.principalIdeles (𝓞 K) K`](def/M4aHerbrand_IdeleClassVocab.html#L16) of principal ideles with respect to [`NumberField.Idele.idelicHaar K`](def/NumberField_IdeleProductMeasure.html#L391); and a constant $V\in(0,\infty)$, $V\neq0$, $V\neq\infty$, such that for every measurable $f:\mathbb R\to\mathbb R_{\ge0}^\infty$ one has $\int^-_{z\in D} f(\|z\|)\,=\,V\int^-_{y>0} f(y)\,y^{-1}$, where $\|\cdot\|=$ [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19).
--
--   **Conclusion (existence of the constant).** There exists a real $C>0$ such that for all data listed next the three assertions below hold. All automorphic notions are taken with respect to the carrier $P:=$ `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose domain is the canonical truncation domain $D_{\alpha\beta}$ for $(\alpha,\beta)$, whose measure is `adelicGLHaar`, whose central subgroup is $\top$, whose level subgroups are $\mathrm{principalLevel}(M)\cap\ker(\mathrm{glArch})$, whose Hecke generators are `heckeGen`, and whose additive measure is `adelicAddHaar` conditioned on the box `adelicBox K`.
--
--   The data are:
--
--   *Cuspidal orthonormal family* (five hypothesis groups): a type $\iota$, functions $b:\iota\to(G\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ`, with `hb` asserting for each $i$ that $\mathrm{cls}\,i$ lies in `cuspClasses K P ξK N SK` (level $N$, vanishing $a_v,b_v$ for $v\in S_K$, nonzero isotypic space) and $b\,i$ lies in `isotypicCuspSubmodule K P ξK N SK (cls i) ⊓ archCutSubmodule K tysK`; `hbn` and `hbo`, normalisation $\int_{D_{\alpha\beta}} b_i\,\overline{b_i}=1$ and orthogonality $\int_{D_{\alpha\beta}} b_i\,\overline{b_j}=0$ for $i\ne j$ against `adelicGLHaar`; `hbs`, that for every cusp class $\pi$ the fibre $\{i:\mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb C$-span of its $b$-values is the full isotypic space intersected with the type cut; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $(P,\xi_K)$, continuous, invariant under right translation by $P.U\,N$, lying in the type cut, and orthogonal to every $b_i$ over $D_{\alpha\beta}$, vanishes almost everywhere for `adelicGLHaar` restricted to $D_{\alpha\beta}$.
--
--   *Eisenstein index family*: a countable type $\iota_E$ and characters $\mu,\nu:\iota_E\to(\mathbb A_K^\times\to\mathbb C^\times)$, each $\mu_e,\nu_e$ unitary (`IsUnitaryChar`), trivial on principal ideles (`IsIdeleClassChar`), continuous, with $\mu_e\nu_e=\xi_K$, and pairwise separated on the norm-one ideles (for $e\ne e'$ some norm-one $z$ has $\mu_e z\ne\mu_{e'}z$ or $\nu_e z\ne\nu_{e'}z$).
--
--   *Flat section families*: $n_E:\iota_E\to\mathbb N$ and $\varphi_{e,j,s}=$ `φE e j s` for $j\in\mathrm{Fin}(n_E e)$, subject to eleven hypothesis groups: each $\varphi_{e,j,s}$ is an induced section for the pair $(\eta^{1}=\mu_e\,\alpha_m^{\,s+1/2},\ \eta^{2}=\nu_e\,\alpha_m^{-(s+1/2)})$, i.e. $\varphi(bg)=\eta^1(b_{00})\eta^2(b_{11})\varphi(g)$ for upper-triangular $b$; archimedean $K$-finiteness and $K_f$-smoothness; joint continuity in $(s,g)$; entirety in $s$ for each $g$; at each infinite place $w$ a single finite-dimensional space $W$ containing all functions $k\mapsto\varphi_{e,j,s}(gk)$ on the row-isometry subgroup; flatness $\varphi_{e,j,s}(k)=\varphi_{e,j,0}(k)$ on `adelicMaximalCompact K`; right invariance under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$; membership in the type cut; orthonormality $\int_{\mathbf K}\varphi_{e,i,0}\overline{\varphi_{e,j,0}}\,d(\mathrm{maximalCompactHaar}\,K)=\delta_{ij}$; a spanning property (`_hφEspan`), that every continuous archimedean $K$-finite, level-invariant, type-cut induced section for the pair at $s=it$ lies in the span of the $\varphi_{e,j,it}$; and exhaustiveness of the index set (`_hpairs`), that for any unitary, idele-class, continuous pair $(\mu',\nu')$ with $\mu'\nu'=\xi_K$ admitting a nonzero such section at $s=it$ there is $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   *Axis continuations*: sets $O_{e,j}\subseteq\mathbb C$ and families $E_{e,j,s},N_{e,j,s}$ with `_hEE` (nine clauses): $O_{e,j}$ is open and preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; $s\mapsto E_{e,j,s}(g)$ and $s\mapsto N_{e,j,s}(g)$ are analytic on a neighbourhood of $O_{e,j}$ for every $g$; both are continuous on $O_{e,j}\times G$; and for $\mathrm{Re}\,s>1/2$ one has $E_{e,j,s}(g)=\varphi_{e,j,s}(g)+\sum_{\xi\in K}\varphi_{e,j,s}(w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix, and $N_{e,j,s}(g)=\int_{\mathbb A_K}\varphi_{e,j,s}(w^{-1}u(x)g)\,d(\mathrm{adelicAddHaar})(x)$.
--
--   *Paley–Wiener datum*: a finite type $\iota_P$, characters $\mu_P,\nu_P:\iota_P\to(\mathbb A_K^\times\to\mathbb C^\times)$, unitary, idele-class, continuous, with $\mu_P(e)(z)\,\nu_P(e)(z)=\xi_K(z)$ for all $z$ in $P.Z=\top$; an involution-type map $r_P:\iota_P\to\iota_P$ with $\mu_P(r_Pe)=\nu_P(e)$ and $\nu_P(r_Pe)=\mu_P(e)$; pairwise separation of the $\iota_P$-indices on norm-one ideles; sections $\psi_{f,e,s}$ which are induced for $(\mu_P(e)\alpha_m^{s+1/2},\nu_P(e)\alpha_m^{-(s+1/2)})$, jointly continuous, holomorphic in $s$, and subject to the vertical-strip decay hypothesis `_hψdec`: for each $e$, each $n\in\mathbb N$, each $\sigma_0$ and each compact $C\subseteq G$ there is an integrable, bounded-above $m:\mathbb R\to\mathbb R$ with $(1+|t|)^n\|\psi_{f,e,\sigma'+it}(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb R$, $g\in C$. Finally a function $\psi:G\to\mathbb C$ which is a `IsSlabProfile` for $(\top,\xi_K)$ — measurable, invariant under left unipotent translation and under left translation by global Borel points, transforming by $\xi_K$ under the adelic centre, bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and supported in a height band — together with the representation `_hψrep`: for every $\sigma'\in\mathbb R$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb R}\psi_{f,e,\sigma'+it}(g)\,dt$.
--
--   *Matching data*: maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb R$ with $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau_i}$ (in terms of `normPowChar`), and `_hNEind`: for all $e,j$ and real $t$, $N_{e,j,it}$ is an induced section for the swapped pair $(\nu_e\,\alpha_m^{-it+1/2},\ \mu_e\,\alpha_m^{it-1/2})$, i.e. for `etaFst (ν e) αm hαm (-(t i))` and `etaSnd (μ e) αm hαm (-(t i))`.
--
--   Writing $v:=$ the real volume `(adelicAddHaar (𝓞 K) K) (adelicBox K)` regarded as a complex number, and $\Theta_{e,j,s}:=\varphi_{e,j,s}+v^{-1}N_{e,j,s}$, the three asserted conjuncts are:
--
--   1.
--
--   (Integrability.) For all $e\in\iota_E$, $j\in\mathrm{Fin}(n_E e)$ and $t\in\mathbb R$, the function $(y,k)\mapsto\psi(\mathrm{diag}(y,1)k)\,\overline{\Theta_{e,j,it}(\mathrm{diag}(y,1)k)}$ on $\mathbb A_K^\times\times\mathbf K$, $\mathbf K=$ `adelicMaximalCompact K`, is integrable for the product of `(idelicHaar K).restrict D` weighted by the density $y\mapsto\|y\|^{-1}$ with `maximalCompactHaar K`.
--
--   2.
--
--   (Vanishing for unmatched indices.) For every $e\in\iota_E$ which is not of the form $\mathrm{em}(i)$ for any $i\in\iota_P$, and all $j$ and all $t\in\mathbb R$,
--   $$\int_{y\in D}\|y\|^{-1}\!\!\int_{\mathbf K}\psi(\mathrm{diag}(y,1)k)\,\overline{\Theta_{e,j,it}(\mathrm{diag}(y,1)k)}\,dk\,d(\text{idelicHaar})=0 .$$
--
--   3.
--
--   (Matched pairings.) For every $i\in\iota_P$, every $j\in\mathrm{Fin}(n_E(\mathrm{em}\,i))$ and every $t\in\mathbb R$, setting $t_E:=i\,(t+\tau_i)$,
--   $$\int_{y\in D}\|y\|^{-1}\!\!\int_{\mathbf K}\psi(\mathrm{diag}(y,1)k)\,\overline{\Theta_{\mathrm{em}(i),j,t_E}(\mathrm{diag}(y,1)k)}\,dk\,d(\text{idelicHaar})$$
--   equals
--   $$C\left(\int_{\mathbf K}\psi_{f,i,it}(k)\,\overline{\varphi_{\mathrm{em}(i),j,t_E}(k)}\,dk+\int_{\mathbf K}\psi_{f,r_P(i),-it}(k)\,\overline{v^{-1}N_{\mathrm{em}(i),j,t_E}(k)}\,dk\right),$$
--   both $\mathbf K$-integrals being taken against `maximalCompactHaar K`, with $C$ the constant produced at the outset, independent of all the data quantified after it.
--
--   This is the torus-side step in Langlands' computation of the continuous-spectrum coefficients of a pseudo-Eisenstein series: unfolding the pairing of a Paley–Wiener profile $\psi$ against the constant term $\varphi+v^{-1}N$ of an Eisenstein section along the diagonal torus and the maximal compact subgroup, with a single frame-dependent positive constant, vanishing whenever the Eisenstein character pair is not among those occurring in $\psi$, and an explicit two-term $\mathbf K$-pairing in the matched case. It is used by [`AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener), which assembles the coefficient formula for the continuous part of the spectral expansion on the truncated domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener.lean

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
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open scoped NNReal ENNReal

theorem AutomorphicForm.exists_forall_setIntegral_inv_ideleNorm_smul_integral_maximalCompact_mul_conj_constantTerm_eq_of_matched_paleyWiener
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
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
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹),
    ∃ C : ℝ, 0 < C ∧
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
      (_hNEind : ∀ (e : ιE) (j : Fin (nE e)) (t : ℝ),
        IsInducedSection (𝓞 K) K (etaFst (ν e) αm hαm (-((t : ℂ) * Complex.I)))
          (etaSnd (μ e) αm hαm (-((t : ℂ) * Complex.I))) (NE e j ((t : ℂ) * Complex.I))),
    (∀ (e : ιE) (j : Fin (nE e)) (t : ℝ),
      Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          ψ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
            conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g)
              (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod (maximalCompactHaar K))) ∧
    (∀ (e : ιE), (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ),
      ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE e j ((t : ℂ) * Complex.I) g + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) = 0) ∧
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
    let vol : ℂ := (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)
    let tE : ℂ := (((t + τ i : ℝ) : ℂ)) * Complex.I
    ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
            ∫ k, ψ (diagOne y * (k : AdelicGL2 (𝓞 K) K)) * conj ((fun g => φE (em i) j tE g + vol⁻¹ * NE (em i) j tE g) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
          ∂(NumberField.Idele.idelicHaar K) =
        (C : ℂ) *
          ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j tE (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj (vol⁻¹ * NE (em i) j tE (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) := by sorry
