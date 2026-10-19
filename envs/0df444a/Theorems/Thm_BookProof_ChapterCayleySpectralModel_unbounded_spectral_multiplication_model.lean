-- Prove2me | Theorems.Thm_BookProof_ChapterCayleySpectralModel_unbounded_spectral_multiplication_model
-- name    : BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:19.105439+00:00
-- url     : https://prove2.me/theorems/7499b40b-24ce-40fb-8d84-15a8ba984060
-- title:
--   `BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model` (hxi : ‖xi‖ = 1) (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) : ∃ (mu : M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCayleySpectralModel`.
--
--   `BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model` (hxi : ‖xi‖ = 1) (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) : ∃ (mu : Measure (spectrum ℂ (cayleyCLM T))) (_ : IsProbabilityMeasure mu) (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H), (∀ u : Lp ℂ 2 mu, ∃ hmem : U (mulRep mu (resSymbol T) u) ∈ T.domain, T.op ⟨U (mulRep mu (resSymbol T) u), hmem⟩ = U (mulRep mu (opSymbol T) u)) ∧ (∀ x : T.domain, ∃ u : Lp ℂ 2 mu, U (mulRep mu (resSymbol T) u) = (x : H))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model`.

-- Generated from ChapterCayleySpectralModel.lean — theorem BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCayleyTransform
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCayleySpectralModel
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterCayleySpectralModel


open scoped InnerProductSpace
open MeasureTheory


open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent
open BookProof.ChapterCayleyTransform BookProof.ChapterAbelianGelfandModel
open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : UnboundedSelfAdjoint H)

variable (xi : H)

theorem BookProof.ChapterCayleySpectralModel.unbounded_spectral_multiplication_model (hxi : ‖xi‖ = 1)
    (hcyc : DenseRange (cfcVec (cayleyCLM T) (isStarNormal_cayleyCLM T) xi)) :
    ∃ (mu : Measure (spectrum ℂ (cayleyCLM T))) (_ : IsProbabilityMeasure mu)
      (U : Lp ℂ 2 mu ≃ₗᵢ[ℂ] H),
      (∀ u : Lp ℂ 2 mu, ∃ hmem : U (mulRep mu (resSymbol T) u) ∈ T.domain,
        T.op ⟨U (mulRep mu (resSymbol T) u), hmem⟩ = U (mulRep mu (opSymbol T) u)) ∧
      (∀ x : T.domain, ∃ u : Lp ℂ 2 mu, U (mulRep mu (resSymbol T) u) = (x : H)) := by sorry
