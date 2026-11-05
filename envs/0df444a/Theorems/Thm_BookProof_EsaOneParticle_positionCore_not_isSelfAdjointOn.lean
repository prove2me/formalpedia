-- Prove2me | Theorems.Thm_BookProof_EsaOneParticle_positionCore_not_isSelfAdjointOn
-- name    : BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T13:45:45.21585+00:00
-- url     : https://prove2.me/theorems/8dda6d7a-de92-42b5-9897-5ea76daecb16
-- title:
--   `BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn` : ¬ IsSelfAdjointOn Dfin positionCore
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaOneParticleDGamma`.
--
--   `BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn` : ¬ IsSelfAdjointOn Dfin positionCore
--
--   Formalization note: Lean 4 identifier `BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn`.

-- Generated from ChapterEsaOneParticleDGamma.lean — theorem BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Mathlib
import Definitions.Def_ChapterEsaOneParticleDGamma
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport



open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A₂ : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier) (hle : D ≤ D₂)
  (hext : ∀ v : D, A₂ ⟨(v : Hs.carrier), hle v.2⟩ = A v)
variable {Hs : IPSpace} {D : Submodule ℂ Hs.carrier}
variable [CompleteSpace Hs.carrier]
variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)
variable {Hs : IPSpace}

theorem BookProof.EsaOneParticle.positionCore_not_isSelfAdjointOn : ¬ IsSelfAdjointOn Dfin positionCore := by sorry
