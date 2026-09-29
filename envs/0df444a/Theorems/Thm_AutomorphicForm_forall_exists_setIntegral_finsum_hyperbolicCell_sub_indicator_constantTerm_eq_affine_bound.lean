-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound
-- name    : AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0cd9bafe-99bd-5217-afe7-0ac08dd93109
-- title:
--   Hyperbolic term affine in the truncation parameter, with bounded coefficients
-- statement:
--   Throughout, $L/K$ is a Galois extension of number fields, $\mathbb{A}_L$ denotes the adele ring of $L$, and $\mathrm{GL}_2(\mathbb{A}_L)$ is written `AdelicGL2 (𝓞 L) L`. The global data are: real numbers $\alpha<\beta$ with $0<\alpha$; a subset $\Phi_L$ of $\mathrm{GL}_2(\mathbb{A}_L)$; a Haar measure $\nu_{Z_L}$ on the idele group $\mathbb{A}_L^\times$ (for a measurable structure which is the Borel structure of the topology) together with a set $\Omega_L$ which, by the hypothesis `hΩL`, is a fundamental domain for the action of the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z_L}$; a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each argument and extends the action on $L$; an element $\sigma$ of $\mathrm{Gal}(L/K)$ with the hypothesis `hgen` that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$; a finite set $S_L$ of finite places of $L$; a character $\xi_L$ of the full subgroup of $\mathbb{A}_L^\times$ with values in $\mathbb{C}^\times$, subject to the continuity hypothesis `hξc` for $z\mapsto\xi_L(z)$ and the triviality hypothesis `hξt` on the image of $L^\times$; a finite set $S$ of finite places of $K$; a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$; and a family $\varphi_S$ of complex functions on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by the finite places $v$ of $K$.
--
--   The geometry of the fundamental domain is fixed by: reals $c,u,d_1,d_2$ with $0<c$; a compact set $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_L)$; and a set $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ satisfying three hypotheses. First, `hΦ₀S`: $\Phi_0$ is contained in the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂`, whose members are those $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and window quantity `xWindowSq` at most $u^2$, and whose archimedean determinant norm at every $w$ lies in $[d_1,d_2]$. Second, `hΦ₀s`: every $g\in\Phi_0$ has $\det g$ of idelic norm (the modulus of the distributive Haar character) in $[\alpha,\beta]$. Third, `hΦ₀`: $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that determinant slab.
--
--   The conclusion is universally quantified over Hecke data, as follows. Let $T$ be a finite set of finite places of $K$ with $2\le\#T$, such that no place of $L$ lying over a place of $T$ belongs to $S_L$. Let $w_\bullet$ assign to each finite place $v$ of $K$ a place $w_v$ of $L$ above $v$, and let $w'$ be a map from finite places of $K$ to finite places of $L$ such that for $v\in T$ the ideal of $w'_v$ is the $\sigma$-translate of the ideal of $w_v$. Let $\varpi_\bullet$ assign to each $v$ an element of the valuation ring of $L_{w_v}$, irreducible for $v\in T$, with nonzero image in $L_{w_v}$ for $v\in T$ (the hypothesis `hϖs0`, which is named and used as an argument of [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68)). Let $n_\bullet:\,v\mapsto n_v$ be natural numbers and $r_{T,\bullet}$ families $r_{T,v}:\mathrm{Fin}\,n_v\to\mathrm{GL}_2(L_{w_v})$ such that for $v\in T$ the family $r_{T,v}$ is a Hecke coset system (each member lies in the double coset of $\mathrm{diag}(\varpi_v,1)$ modulo the integral subgroup $\mathrm{GL}_2(\mathcal{O}_{w_v})$, the members cover that double coset modulo the integral subgroup on the right, and they are pairwise distinct modulo it). Finally let $z_\bullet$ assign to each $v$ an element of $\mathrm{GL}_2(L_{w_v})$ whose matrix, for $v\in T$, is the scalar $\varpi_v$ times the identity.
--
--   Under these assumptions there exist two functions $\mu,\nu$ of two variables $k_\bullet,j_\bullet$ ranging over natural-number-valued functions on the finite places of $K$, with values in $\mathbb{C}$, such that the following two assertions hold.
--
--   (i) Uniform bound: there is a real $C$ with
--   $$\|\mu(k_\bullet,j_\bullet)\|+\|\nu(k_\bullet,j_\bullet)\|\le C\prod_{v\in T}\Big((\,\mathrm{absNorm}(w'_v)+1)\sqrt{|\xi_L(\det \mathrm{heckeGen}(w'_v))|}\Big)^{k_v}\,|\xi_L(\det \mathrm{heckeGen}(w'_v))|^{j_v}$$
--   for all $k_\bullet,j_\bullet$, where $\mathrm{heckeGen}(w)$ is the adelic matrix `heckeGen (𝓞 L) L w` which is $\mathrm{diag}(\varpi_w,1)$ at $w$ and the identity elsewhere.
--
--   (ii) Affine identity: for all $k_\bullet,j_\bullet$, every $\varphi:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds for the family of local components which equals $\varphi_S(v)$ for $v\notin T$ and, for $v\in T$, is the function
--   $$x\longmapsto\sum_{\iota:\mathrm{Fin}\,k_v\to\mathrm{Fin}\,n_v}\mathbf{1}_{\mathcal{I}_v}\Big(\big(\text{(semi-local component at }v)\big(\text{embedding at }w_v\text{ of }\textstyle\prod_{m}r_{T,v}(\iota\,m)\cdot z_v^{\,j_v}\big)\big)^{-1}x\Big),$$
--   $\mathcal{I}_v$ being the set of elements of $\mathrm{GL}_2(L\otimes_K K_v)$ which together with their inverses have entries in the image of the integers of $L$ at the places above $v$ — that is, $\varphi$ factors as $\varphi_a$ on the archimedean part times $\varphi_f$ on the finite part, $\varphi_a$ is a smooth compactly supported archimedean test factor, $\varphi_f$ is locally constant with compact support, each local component at a place of $S\cup T$ is locally constant with compact support, $\varphi_f$ is the product of the local components over $S\cup T$ at matrices integral outside $S\cup T$, and vanishes at matrices non-integral at some place outside $S\cup T$ — there exists $R_0\in\mathbb{R}$ such that for every $R\ge R_0$ the following three statements hold.
--
--   Write, for $x\in\mathrm{GL}_2(\mathbb{A}_L)$ and $z\in\mathbb{A}_L^\times$,
--   $$\Psi(x,z)=\xi_L(z)\Big(\sum_{\delta\in\mathcal{H}}\varphi\big(x^{-1}\,\delta\,\sigma_{\mathbb{A}}(c(z)x)\big)-\mathbf{1}_{\{H>e^{R}\}}(c(z)x)\cdot \mathrm{CT}_x(c(z)x)\Big),$$
--   where: the sum is the finite-support sum over the set $\mathcal{H}$ of those $\delta\in\mathrm{GL}_2(L)$ for which there is a $\gamma$ in [`AutomorphicForm.hyperbolicCell K`](def/AutomorphicForm_GL2ConjugacyCells.html#L32) (matrices whose characteristic polynomial splits over $K$ with two distinct roots) with `normClassMap hgen` of the $\sigma$-conjugacy class of $\delta$ equal to the conjugacy class of $\gamma$; $\delta$ is viewed in $\mathrm{GL}_2(\mathbb{A}_L)$ through `globalPoints`, $c(z)=\mathrm{diag}(z,z)$ is `centralScalar`, and $\sigma_{\mathbb{A}}$ is the action `sigmaAdelicAct K L D σ` of $\sigma$ on $\mathrm{GL}_2(\mathbb{A}_L)$ through $D$; $H$ is the adelic height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) and $\{H>e^R\}$ is the corresponding high set; and $\mathrm{CT}_x$ is the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) taken with respect to the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$ and the measure obtained from `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L) (adelicBox L)`, namely the additive Haar measure of $\mathbb{A}_L$ conditioned on the adelic box (the fundamental box at the infinite places together with the integral finite adeles), of the function
--   $$y\longmapsto \sum_{\delta\in\mathcal{B}}\varphi\big(x^{-1}\,\delta\,\sigma_{\mathbb{A}}(y)\big),\qquad \mathcal{B}=\{\gamma\in\mathrm{GL}_2(L):\gamma_{10}=0,\ N_{L/K}(\gamma_{00}/\gamma_{11})\ne 1\}.$$
--
--   Then: (a) for every $x\in\mathrm{GL}_2(\mathbb{A}_L)$ the function $z\mapsto\Psi(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z_L}$; (b) the function $x\mapsto\int_{\Omega_L}\Psi(x,z)\,d\nu_{Z_L}(z)$ is integrable on $\Phi_0$ with respect to `adelicGLHaar`; and (c)
--   $$\int_{\Phi_0}\int_{\Omega_L}\Psi(x,z)\,d\nu_{Z_L}(z)\,dx=R\cdot\nu(k_\bullet,j_\bullet)+\mu(k_\bullet,j_\bullet),$$
--   with $R$ read as a complex number. Thus the truncated hyperbolic contribution, attached to the Hecke word of length $k_v$ in the coset representatives at $v$ twisted by the $j_v$-th central power, is an affine function of the truncation parameter $R$ with coefficients independent of $R$ and of $\varphi$, bounded as in (i).
--
--   This is the hyperbolic-type term on the geometric side of the truncated twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, evaluated against a Hecke word at the places of $T$: the result packages the affine dependence on the truncation parameter together with a bound on the two coefficients in terms of the residue degrees at the transported places $w'_v$ and the values of the central character on the corresponding Hecke generators. It combines the bare affine identity [`AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare`](thm.html#AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare) with the coefficient bound [`AutomorphicForm.exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine`](thm.html#AutomorphicForm.exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine), and feeds the assembly of the geometric side in [`AutomorphicForm.forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram`](thm.html#AutomorphicForm.forall_exists_integral_lambdaT_twistedAdelicKernel_eq_finsum_centralElliptic_add_and_norm_le_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ,
      (∃ C : ℝ, ∀ ks js : HeightOneSpectrum (𝓞 K) → ℕ,
        ‖μ ks js‖ + ‖ν ks js‖ ≤ C * ∏ v ∈ T,
          ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖) ^ ks v *
            ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ^ js v)) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (R : ℂ) * ν ks js + μ ks js := by sorry
