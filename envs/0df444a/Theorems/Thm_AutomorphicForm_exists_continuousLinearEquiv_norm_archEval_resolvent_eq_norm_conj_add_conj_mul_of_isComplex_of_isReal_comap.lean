-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
-- name    : AutomorphicForm.exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/29f60d19-f812-5e5c-89df-059e38f4d1f4
-- title:
--   Twisted resolvent at a complex place over a real place
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and suppose $[L:K]$ is prime. Equip $E := L \otimes_K K_\infty$ (with $K_\infty$ the infinite adele ring of $K$) with a measurable structure that is the Borel structure of its topology and with an additive Haar measure $\lambda$. Let $w$ be a real infinite place of $K$ and $w'$ a complex infinite place of $L$ with $w'$ restricting to $w$ along $K \to L$. Write $\iota : E \to \mathbb{A}_{L,\infty}$ for the ring map `archIdent`, i.e. the commutativity isomorphism $L \otimes_K K_\infty \cong K_\infty \otimes_K L$ followed by the base-change isomorphism $K_\infty \otimes_K L \cong \mathbb{A}_{L,\infty}$ attached to `genuineInfinitePlaceData`, and let $z(y) \in \mathbb{C}$ denote the $w'$-coordinate of the image of $\iota(y)$ under the identification of $\mathbb{A}_{L,\infty}$ with the mixed space of $L$. The assertion is that there exist a continuous $\mathbb{R}$-linear isomorphism $e$ from the mixed space of $L$ onto $\mathbb{C} \times \big((\{v : v \text{ real}\} \to \mathbb{R}) \times (\{v : v \text{ complex}, v \neq w'\} \to \mathbb{C})\big)$ and a nonzero $\kappa \in \mathbb{R}_{\geq 0}$ such that: the pushforward of $\lambda$ along $y \mapsto e(\iota(y))$ is $\kappa$ times the product of Lebesgue measure on $\mathbb{C}$ with the product of the Lebesgue measures on the two remaining factors; the first coordinate of $e(\iota(y))$ equals $z(y)$ for all $y$; and, for every $r \in E$ and every unit $c$ of $K_\infty$ with $c = 1 - N_{K_\infty}(r)$ (the algebra norm of $r$ over $K_\infty$), and every $K_\infty$-linear endomorphism $M$ of $E$ satisfying both $(\sigma \otimes \mathrm{id})(M y) - r \cdot M y = c \cdot y$ and $M\big((\sigma \otimes \mathrm{id})(y) - r \cdot y\big) = c \cdot y$ for all $y$, one has $\|\iota(M y)_{w'}\| = \|\overline{z(y)} + \overline{z(r)}\, z(y)\|$ for all $y \in E$, together with $\|c_w\| = |1 - \|z(r)\|^2|$, where $c_w$ is the $w$-component of $c$ in the completion at $w$.
--
--   This is the archimedean local analysis of the twisted resolvent at an inert place: when $[L:K]$ is prime and a complex place $w'$ of $L$ lies over a real place $w$ of $K$, the degree is forced to be $2$, $\sigma$ induces complex conjugation on $L_{w'} \cong \mathbb{C}$, and the resolvent acts in the $w'$-coordinate by $z \mapsto \bar z + \overline{z(r)} z$ while the norm factor becomes $|1 - |z(r)|^2|$. It supplies the coordinate normalisation and measure comparison used in the subsequent construction of a smooth compactly supported test function whose orbital integral computes the relevant logarithmic integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap.lean

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

theorem AutomorphicForm.exists_continuousLinearEquiv_norm_archEval_resolvent_eq_norm_conj_add_conj_mul_of_isComplex_of_isReal_comap
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w : NumberField.InfinitePlace K) (w' : NumberField.InfinitePlace L) (hw'w : w'.comap (algebraMap K L) = w)
    (hw : w.IsReal) (hw' : w'.IsComplex) :
    ∃ (e : NumberField.mixedEmbedding.mixedSpace L ≃L[ℝ] (ℂ × (({v : NumberField.InfinitePlace L // v.IsReal} → ℝ) × ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) (κ : NNReal), κ ≠ 0 ∧
      Measure.map (fun y : (L ⊗[K] InfiniteAdeleRing K) => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) lam =
        κ • ((volume : Measure ℂ).prod
          ((volume : Measure ({v : NumberField.InfinitePlace L // v.IsReal} → ℝ)).prod
            (volume : Measure ({v : {v : NumberField.InfinitePlace L // v.IsComplex} // v ≠ ⟨w', hw'⟩} → ℂ)))) ∧
      (∀ y : (L ⊗[K] InfiniteAdeleRing K), (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))).1 = (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) ∧
      ∀ (r : (L ⊗[K] InfiniteAdeleRing K)) (c : (InfiniteAdeleRing K)ˣ),
        (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r →
      ∀ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K),
        (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) →
        (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) →
      (∀ y : (L ⊗[K] InfiniteAdeleRing K),
        ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ =
          ‖(starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩) +
            (starRingEnd ℂ) ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L r)).2 ⟨w', hw'⟩) * (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)).2 ⟨w', hw'⟩‖) ∧
      ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ =
        |1 - ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L r)).2 ⟨w', hw'⟩‖ ^ 2| := by sorry
