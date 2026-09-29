-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
-- name    : AutomorphicForm.setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fbe2dffd-f24b-5b4d-b659-bcc89a891aaf
-- title:
--   Non-σ-invariant idele character kills the truncated unipotent term
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $0<\alpha<\beta$ be reals, let $\Phi_L$ be a subset of $\mathrm{GL}_2$ of the adeles of $L$, let $\nu_{Z_L}$ be a Haar measure on the idele group $\mathbb{A}_L^\times$ and $\Omega_L$ a fundamental domain for the subgroup of principal ideles (the range of $L^\times\to\mathbb{A}_L^\times$) with respect to $\nu_{Z_L}$. Let $D$ be a descent datum: a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with the Galois action on $L$ and continuous. Let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the group of integral powers of $\sigma$; let $S_L$ be a finite set of primes of $\mathcal{O}_L$ containing every $w$ whose ramification index over its restriction to $K$ is not $1$; let $\xi_L$ be a homomorphism from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function and trivial on the principal ideles; let $S$ be a finite set of primes of $K$, $\varphi_a$ a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S$ a family of functions on $\mathrm{GL}_2(L\otimes_K K_v)$. Let $c>0$, $u$, $d_1$, $d_2$ be reals, $T_c$ a compact set, and $\Phi_0$ a set contained in the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set of $L$ with parameters $c,u,d_1,d_2$ (finite part integral, all local heights at least $c$, all window quantities at most $u^2$, archimedean determinant norms in $[d_1,d_2]$), contained in the shell where the idele norm of the determinant lies in $[\alpha,\beta]$, and a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic $\mathrm{GL}_2$ Haar measure restricted to that shell. The assertion is then: for every finite set $T$ of primes of $K$ none of whose primes of $L$ above it lies in $S_L$; every family $ws$ assigning to each $v$ an extension of $v$ to $\mathcal{O}_L$, and every $w'$ with $(w'v)$ equal to the $\sigma$-translate of $(ws\,v)$ for $v\in T$; every family $\varpi_s$ of elements of the valuation rings of the completions $L_{ws\,v}$, irreducible with nonzero image in $L_{ws\,v}$ for $v\in T$; every $ns$ and every family $rT_s\,v:\mathrm{Fin}(ns\,v)\to\mathrm{GL}_2(L_{ws\,v})$ which for $v\in T$ is a system of coset representatives for the double coset of $\mathrm{diag}(\varpi_s v,1)$ modulo the image of $\mathrm{GL}_2$ of the valuation ring (representatives in the double coset, covering it modulo the subgroup, with pairwise distinct classes); every $zs$ with $zs\,v$ the scalar matrix $\varpi_s v\cdot 1$ for $v\in T$; assuming that $\xi_L$ is not invariant under the action of $\sigma$ on $\mathbb{A}_L^\times$ induced by $D$, i.e.\ some $z_0$ has $\xi_L(\sigma z_0)\neq\xi_L(z_0)$; and for all $ks$, $js$ and all $\varphi$, $\varphi_f$ satisfying the semi-local factorization condition over $S\cup T$ (with $\varphi_a$ smooth of compact support in the archimedean matrix entries, $\varphi_f$ locally constant of compact support, each local factor locally constant of compact support, $\varphi_f$ equal to the product of the local factors at $S\cup T$ on elements whose components off $S\cup T$ are integral and zero otherwise, and $\varphi$ the product of $\varphi_a$ on the archimedean part with $\varphi_f$ on the finite part), the local factor at $v\in T$ being $x\mapsto\sum_{\iota:\mathrm{Fin}(ks\,v)\to\mathrm{Fin}(ns\,v)}$ of the indicator of the semi-local integral set of $\mathrm{GL}_2(L\otimes_K K_v)$ at the semi-local component of the inverse of the place-$ws\,v$ embedding of $\prod_m rT_s\,v(\iota\,m)\cdot (zs\,v)^{js\,v}$ times $x$, and $\varphi_S v$ off $T$ — there exists $R_0$ such that for every $R\ge R_0$ the integral over $x\in\Phi_0$, with respect to the adelic $\mathrm{GL}_2$ Haar measure, of the integral over $z\in\Omega_L$ with respect to $\nu_{Z_L}$ of $\xi_L(z)$ times the difference between the sum over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma$-twisted norm class maps to the class of some $\gamma\in\mathrm{GL}_2(K)$ of unipotent type (not central, with characteristic polynomial a square $(X-a)^2$) of $\varphi\bigl(x^{-1}\,\delta\,\sigma(z\cdot x)\bigr)$, where $\delta$ acts through the global points map, $z$ through the central scalar embedding and $\sigma$ through $D$, and the value at $z\cdot x$ of the indicator, on the set where the adelic height of $L$ exceeds $e^R$, of the constant term $g\mapsto\int f\bigl(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\bigr)g)\,dt$ taken with respect to the Borel structure and the additive adelic Haar measure conditioned on the adelic box of $L$, with $f(y)=\sum\varphi\bigl(x^{-1}\,\delta\,\sigma(y)\bigr)$ over those $\delta\in\mathrm{GL}_2(L)$ with lower-left entry $0$ and $N_{L/K}(\delta_{00}/\delta_{11})=1$, is equal to $0$.
--
--   This is the central-character gate for the unipotent-type contribution to the $\sigma$-twisted kernel: only data whose central character is invariant under the Galois action on the ideles can contribute, so a non-$\sigma$-invariant $\xi_L$ makes the truncated unipotent term vanish for all sufficiently large truncation parameters. It is used by the downstream evaluations of this term as a sum of rank-one integrals and as a weighted moment expression in the unramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram.lean

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

theorem
    AutomorphicForm.setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_zero_of_not_sigmaInvariant_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
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
            ¬ (∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
        ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩) →
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
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = 0 := by sorry
