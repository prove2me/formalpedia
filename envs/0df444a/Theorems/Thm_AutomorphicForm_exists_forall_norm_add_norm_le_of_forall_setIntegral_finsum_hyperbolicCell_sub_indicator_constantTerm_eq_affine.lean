-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine
-- name    : AutomorphicForm.exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/cb41b889-df31-5a4b-95ba-181b679d9499
-- title:
--   Bounding the affine coefficients of the hyperbolic twisted term
-- statement:
--   Let $L/K$ be a Galois extension of number fields, $0<\alpha<\beta$, $\Phi_L$ a set of adelic $\mathrm{GL}_2(L)$-matrices, $\nu_{Z_L}$ a Haar measure on the idele group of $L$ with $\Omega_L$ a fundamental domain for the image of $L^\times$, $D$ a descent datum giving a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$ compatible with $L$ and continuous, $\sigma$ an element whose integral powers exhaust $\mathrm{Gal}(L/K)$, $S_L$ a finite set of primes of $\mathcal{O}_L$, $\xi_L$ a character of the full idele group with continuous complex values and trivial on $L^\times$, $S$ a finite set of primes of $\mathcal{O}_K$, $\varphi_a$ an archimedean factor, $\varphi_S$ semi-local factors, reals $c>0,u,d_1,d_2$, a compact $T_c$, and $\Phi_0$ contained in $\bigcup_{y\in T_c}(\cdot\, y)$-translates of the centre-cut Siegel set for $(c,u,d_1,d_2)$ and in the slab where the idele norm of the determinant lies in $[\alpha,\beta]$, and a fundamental domain for $\mathrm{GL}_2(L)$ with respect to adelic Haar measure restricted to that slab. The assertion: for every finite $T$ of primes of $K$ with $\#T\ge 2$ and no prime of $L$ over $T$ in $S_L$, every choice of $w_v\mid v$, of $w'_v$ with ideal $\sigma\cdot w_v$, of uniformisers $\varpi_v$ (irreducible, nonzero in the completion), of $n_v$ and of $r_{v,i}$ forming a Hecke coset system for the integral subgroup $\mathrm{GL}_2(\mathcal{O}_{w_v})$-image and $\mathrm{diag}(\varpi_v,1)$ (representatives lying in the double coset, covering it modulo the subgroup, with distinct cosets), and of $z_v=\varpi_v\cdot 1$, there is $C\ge 0$ such that: for all exponent functions $k,j$, all $\varphi$ and $\varphi_f$ satisfying the semi-local factorisation condition over $S\cup T$ with factors $\varphi_a$, $\varphi_f$ and, at $v\in T$, the function $x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\text{integral set}}\bigl(\text{semi-local component of }(\prod_m r_{v,\iota(m)})z_v^{j_v}\text{ embedded at }w_v\bigr)^{-1}x\bigr)$ and $\varphi_S$ elsewhere, and all $\mu_0,\nu_0\in\mathbb{C}$, $R_0\in\mathbb{R}$: if for every $R\ge R_0$ the integral over $x\in\Phi_0$ and $z\in\Omega_L$ of $\xi_L(z)$ times the difference of $\sum_\delta \varphi\bigl(x^{-1}\delta\,\sigma_{\mathbb{A}}(\mathrm{diag}(z,z)x)\bigr)$, over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma$-twisted norm class maps to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ with characteristic polynomial having two distinct roots, and the indicator of $\{\text{adelic height}>e^R\}$ times the constant term $y\mapsto\int \sum_{\delta}\varphi\bigl(x^{-1}\delta\,\sigma_{\mathbb{A}}(u(t)y)\bigr)\,d\nu$ (with $u(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, $\nu$ the additive adelic Haar measure conditioned on the adelic box, and $\delta$ running over $\gamma$ with $\gamma_{10}=0$ and $N_{L/K}(\gamma_{00}/\gamma_{11})\ne 1$), evaluated at $\mathrm{diag}(z,z)x$, equals $R\nu_0+\mu_0$, then $\|\mu_0\|+\|\nu_0\|\le C\prod_{v\in T}\bigl((\mathrm{N}(w'_v)+1)\sqrt{\|\xi_L(\det \text{heckeGen}(w'_v))\|}\bigr)^{k_v}\|\xi_L(\det \text{heckeGen}(w'_v))\|^{j_v}$.
--
--   This is the quantitative half of the analysis of the hyperbolic-type contribution to the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L/K$: the truncated hyperbolic term is affine in the truncation parameter $R$, and its constant and linear coefficients are bounded in terms of the symbol of the Hecke word $\prod r_{v,\iota(m)}\cdot z_v^{j_v}$ at the places of $T$. It is combined with the corresponding identity statement in [`AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound`](thm.html#AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine.lean

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

theorem AutomorphicForm.exists_forall_norm_add_norm_le_of_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine
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
      ∃ C : ℝ, 0 ≤ C ∧
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
      ∀ (μ₀ ν₀ : ℂ) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
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
      (R : ℂ) * ν₀ + μ₀) →
        ‖μ₀‖ + ‖ν₀‖ ≤ C * ∏ v ∈ T,
          ((((Ideal.absNorm (w' v).asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖) ^ ks v *
            ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
              ℂˣ) : ℂ)‖ ^ js v) := by sorry
