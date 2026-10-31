-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicModel_cyclic_representation_multiplication_model_of_cyclic_explicit
-- name    : BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_of_cyclic_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:44.927981+00:00
-- url     : https://prove2.me/theorems/1876efed-389f-41b2-9887-c4c40445f06d
-- title:
--   Cyclic representations of $C(X)$ are multiplication models
-- statement:
--   Let $\pi$ be a representation of $C(X)$ on $H$ with cyclic unit vector $\xi$.  Then there is a probability measure $\mu$ on $X$ and a unitary $U \colon L^{2}(\mu) \to H$ intertwining the representation with multiplication:
--   $$U(\mathrm{mulRep}(\mu, g)\,u) = \pi(g)(U u), \qquad U^{-1}\pi(g)v = \mathrm{mulRep}(\mu, g)\,U^{-1}v .$$
--
--   This is the Abelian Gelfand–Naimark–Segal model: the state $g \mapsto \langle \pi(g)\xi,\xi\rangle$ is integrated to $\mu$, and cyclicity makes the resulting map unitary rather than merely isometric.
--
--   Corrected statement of the retired node `BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model`, where the cyclicity hypothesis had been dropped from the exported target.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterAbelianCyclicModel.lean

-- Corrected statement of BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterAbelianCyclicModel.lean (Lean 4.28) and timepiece331/BookProof/ChapterAbelianCyclicModel.lean (Lean 4.33.1).
import Definitions.Def_ChapterAbelianGelfandModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicModel
open BookProof.ChapterAbelianCyclicModel


open MeasureTheory Complex WeakDual
open scoped ComplexOrder


open BookProof.ChapterAbelianGelfandModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)

variable (hcyc : DenseRange (repVec pi xi))

theorem BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model_of_cyclic_explicit (hcyc : DenseRange (repVec pi xi)) (hxi : ‖xi‖ = 1) : ∃ (mu : Measure X) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H), (∀ (g : C(X, ℂ)) (u : Lp ℂ 2 mu), U (mulRep mu g u) = pi g (U u)) ∧ (∀ (g : C(X, ℂ)) (v : H), U.symm (pi g v) = mulRep mu g (U.symm v)) := by sorry
