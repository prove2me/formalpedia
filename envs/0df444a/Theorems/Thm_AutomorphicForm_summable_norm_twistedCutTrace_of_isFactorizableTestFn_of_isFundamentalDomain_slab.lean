-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_twistedCutTrace_of_isFactorizableTestFn_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.summable_norm_twistedCutTrace_of_isFactorizableTestFn_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/687d0733-02c0-57f1-a8ab-c513cbf631c7
-- title:
--   Summability of twisted cut traces over cuspidal classes
-- statement:
--   Let $F$ be a field and $L$ a number field that is an $F$-algebra, let $D$ be a datum consisting of a homomorphism from the group of $F$-algebra automorphisms of $L$ to the ring automorphisms of the adele ring of $L$, each continuous and compatible with the embedding of $L$, and let $\sigma$ be an $F$-algebra automorphism of $L$. Let $0<\alpha<\beta$ be reals, write $G=\mathrm{GL}_2$ over the adeles of $L$ and let $\Phi$ be a subset of the slab $\{g : \lvert\det g\rvert\in[\alpha,\beta]\}$, where $\lvert\cdot\rvert$ denotes the module of an idele given by the distributive Haar character, which is a fundamental domain for the image of $G(L)$ acting on $G$ with respect to the Haar measure of $G$ (for its Borel structure) restricted to that slab. Let $N'\mapsto U(N')$ assign a subgroup of $G$ to each ideal of $\mathcal{O}_L$, let $w\mapsto \mathrm{gen}(w)$ assign an element of $G$ to each finite place, let $\xi$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$, let $N\neq 0$ be an ideal and $S$ a finite set of finite places such that for every $w\notin S$ there are an idele unit $z$ and $u_1,u_2\in U(N)$ with $\mathrm{gen}(w)^{-1}=z\,u_1\,\mathrm{gen}(w)\,u_2$, $z$ viewed as a central scalar matrix. Let $\mathrm{tys}$ be an archimedean type family for $L$, i.e. a number $\mathrm{card}(w)$ of archimedean representation types $\mathrm{rep}(w,i)$ at each infinite place $w$ of $L$, and let $f:G\to\mathbb{C}$ be continuous with compact support and factorizable: $f(g)=f_\infty(g_\infty)f^\infty(g^{\infty})$ with $f_\infty$ smooth of compact support as a function of the matrix entries in the mixed space, and $f^\infty$ locally constant of compact support on $\mathrm{GL}_2$ of the finite adeles. Then the family of real numbers $\lVert \mathrm{twistedCutTrace}\,F\,L\,D\,\sigma\,\ldots\,\pi\,\mathrm{tys}\,f\rVert$ is summable as $\pi$ ranges over the cuspidal classes for the carrier data built from $\Phi$, $U$, $\mathrm{gen}$ and the adelic box (infinite part in the infinite box, finite part integral), with central group the full idele unit group, Haar measure on $G$ and the conditional additive adelic Haar measure on the box: that is, over those Hecke eigensystems of level $N$ whose parameters $a_v,b_v$ vanish for $v\in S$ and whose isotypic cuspidal submodule is nonzero; here the twisted cut trace is the $\sigma$-twisted trace of right convolution by $f$ on the intersection of that isotypic cuspidal submodule with the archimedean cut submodule determined by $\mathrm{tys}$.
--
--   This is the absolute convergence of the spectral side of the (twisted) trace formula for $\mathrm{GL}_2$ over a number field, in the form needed to rearrange sums over cuspidal Hecke eigensystems. It is used in the comparison of Hecke word sums of twisted and untwisted cut traces, and in the computation of fibre sums at central elliptic elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_twistedCutTrace_of_isFactorizableTestFn_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.summable_norm_twistedCutTrace_of_isFactorizableTestFn_of_isFundamentalDomain_slab
    (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L) (σ : L ≃ₐ[F] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L)) (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hstd : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L), u₁ ∈ U N ∧ u₂ ∈ U N ∧
        (gen w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * gen w * u₂)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hft : IsFactorizableTestFn L f) :
    Summable (fun π : ↥(cuspClasses L
        (productionPinsOf L Φ U gen (adelicBox L))
        ξ N S) =>
      ‖twistedCutTrace F L D σ
          (productionPinsOf L Φ U gen (adelicBox L))
          ξ N S π tys f hf hfc‖) := by sorry
