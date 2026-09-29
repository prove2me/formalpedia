-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/36ba4d48-98cf-557c-82b6-8894b4b5328f
-- title:
--   Twisted archimedean log integral at a complex place over a real place
-- statement:
--   Let $L/K$ be an extension of number fields that is finite and Galois, with $\sigma$ an automorphism whose integral powers exhaust $\mathrm{Gal}(L/K)$ and with $[L:K]$ prime; fix Borel-measurable structures on $E := L\otimes_K K_\infty$ (where $K_\infty$ is the infinite adele ring of $K$) and on $E^\times$, an additive Haar measure $\lambda$ on $E$, and a Haar measure $\theta$ on the kernel $U_1$ of the norm map $E^\times \to K_\infty^\times$. Let $\Phi$ be a smooth, compactly supported function of three variables in the mixed space of $L$ whose support has its first two coordinates carried, through [`AutomorphicForm.archIdent`](def/AutomorphicForm_TwistedOrbital.html#L420) followed by `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace`, by a fixed compact set of pairs of units of $E$. Let $w$ be a real place of $K$ and $w'$ a complex place of $L$ with $w'|_K = w$. The assertion is the existence of smooth, compactly supported $A,B$ of two mixed-space variables over $K$, with $\operatorname{tsupport}A \cup \operatorname{tsupport}B$ carried in the same sense by a compact set of pairs of units of $K_\infty$, such that: for all units $a,t$ of $K_\infty$ with $t_v \neq 1$ at every infinite place $v$ of $K$, all units $\alpha,\beta$ of $E$ with $\prod_{i<[L:K]}\sigma^i(\mathrm{diag}(\alpha,\beta)) = \mathrm{diag}(a,at)$ (the latter pushed into $GL_2(E)$ along $K_\infty \to E$), and every family $u \mapsto M_u$ of $K_\infty$-linear endomorphisms of $E$ indexed by pairs $u \in U_1 \times U_1$ satisfying the two-sided twisted resolvent identities $\sigma(M_u y) - r_u M_u y = (1-t)\cdot y$ and $M_u(\sigma y - r_u y) = (1-t)\cdot y$ for all $y$, where $r_u = (\alpha u_1)^{-1}(\beta u_2)$, the function $u \mapsto \int_E \Phi(\iota(\alpha u_1), \iota(\beta u_2), \iota y)\,\log\bigl(\|(1-t)_w\|^2 + \|(M_u y)_{w'}\|^2\bigr)\,d\lambda(y)$ is $\theta\otimes\theta$-integrable, and its integral equals $A(\iota t, \iota a) + \|(1-t)_w\|\,B(\iota t,\iota a)$. Here $\iota$ is [`AutomorphicForm.archIdent`](def/AutomorphicForm_TwistedOrbital.html#L420) followed by `ringEquiv_mixedSpace`, and $x_w$, $x_{w'}$ denote the components [`NumberField.AdelicLevel.archEval`](def/NumberField_AdelicLevel.html#L137) at $w$ and $w'$.
--
--   This is the archimedean local ingredient, at an inert real place of $K$ with complex extension $w'$ in $L$ (possible only in the quadratic case), of the comparison of twisted orbital integrals with weighted logarithmic potentials used in cyclic base change for $GL_2$. It feeds the global assembly of the twisted log weight in [`AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_mul_of_isComplex_place
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ)
    (hΦu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))))
    (w : NumberField.InfinitePlace K) (w' : NumberField.InfinitePlace L) (hw'w : w'.comap (algebraMap K L) = w)
    (hw : w.IsReal) (hw' : w'.IsComplex) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), (∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1) →
      ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
      ∀ (Mu : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ((L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))),
        (∀ u, (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (Mu u y) - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * Mu u y =
              ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) • y) ∧
          (∀ y, Mu u (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y) =
              ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) • y)) →
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
          ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam) (θ.prod θ) ∧
        ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] *
            (Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (Mu u y))‖ ^ 2) : ℂ) ∂lam ∂(θ.prod θ) =
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
          ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by sorry
