-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_setIntegral_mul_finsum_unipotentNormClass_sub_indicator_constantTerm_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_finsum_unipotentNormClass_sub_indicator_constantTerm_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/f289b18f-9ed5-5559-8b75-fc38b19b9270
-- title:
--   Integrability of the truncated σ-twisted unipotent term
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, let $0<\alpha<\beta$ be reals, let $\nu_{Z}$ be a Haar measure on the idele units $\mathbb{A}_L^{\times}$ (with its Borel structure) and let $\Omega\subseteq\mathbb{A}_L^{\times}$ be a fundamental domain for the subgroup of principal ideles, the range of $L^{\times}\to\mathbb{A}_L^{\times}$, with respect to $\nu_Z$. Let $D$ be an idele Galois descent datum for $L/K$, that is, a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{RingAut}(\mathbb{A}_L)$ whose members are continuous and extend the Galois action on principal adeles, and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the group of integral powers of $\sigma$. Let $\xi$ be a homomorphism from the full group $\mathbb{A}_L^{\times}$ (as top subgroup) to $\mathbb{C}^{\times}$ which is continuous as a $\mathbb{C}$-valued function and trivial on principal ideles, and let $\varphi\colon\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ be a factorizable test function: $\varphi(g)=f_{\infty}(g_{\infty})f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_{\infty}$ given by a smooth function of the archimedean matrix entries and compactly supported, and $f_{\mathrm{fin}}$ locally constant with compact support. Write $\iota$ for $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$, $c(z)$ for the central scalar matrix of an idele $z$, $n(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, and $\sigma_{\mathbb{A}}$ for the entrywise automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D$ at $\sigma$. Then there is $R_0\in\mathbb{R}$ such that for every $R\ge R_0$ the function
--   $$x\longmapsto \int_{\Omega}\xi(z)\Big(\sum_{\delta\in S}\varphi\big(x^{-1}\,\iota(\delta)\,\sigma_{\mathbb{A}}(c(z)x)\big)-\mathbf{1}_{\{H>e^{R}\}}(c(z)x)\,F_x(c(z)x)\Big)\,d\nu_Z(z)$$
--   is integrable on [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) — the set selected by the classical choice of a truncation datum for $L,\alpha,\beta$, and empty if none exists — with respect to the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_L)$. Here the finite-support sum runs over the set $S$ of $\delta\in\mathrm{GL}_2(L)$ whose twisted norm class [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) of the $\sigma$-conjugacy class of $\delta$ is the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ that is of unipotent type, i.e. not of central type and with characteristic polynomial $(X-a)^2$ for some $a\in K$; $H$ is the adelic height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), the product of the archimedean and finite heights; and $F_x(g)=\int n(t)$-translate average $\sum_{\delta}\varphi\big(x^{-1}\iota(\delta)\,\sigma_{\mathbb{A}}(n(t)g)\big)\,d\mu(t)$, the constant term taken with respect to the additive adelic Haar measure conditioned on the adelic box of $L$, the inner finite-support sum running over those $\delta\in\mathrm{GL}_2(L)$ with lower-left entry $0$ and $N_{L/K}(\delta_{00}/\delta_{11})=1$.
--
--   This is the absolute convergence, for all sufficiently large truncation parameters, of the unipotent contribution to the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over the canonical truncation domain, the class sum being corrected above the height cutoff by the unipotent (constant-term) average of the upper-triangular part of the kernel with diagonal ratio of norm one. It feeds the assembly of the truncated geometric side, being used in the statement combining the twisted hyperbolic and twisted unipotent cells.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_integrableOn_setIntegral_mul_finsum_unipotentNormClass_sub_indicator_constantTerm_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_finsum_unipotentNormClass_sub_indicator_constantTerm_canonicalTruncationDomain
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφf : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                γ ∈ AutomorphicForm.unipotentCell K ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
            Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
              (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
                (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
                  (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                    Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
              (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
