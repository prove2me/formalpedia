-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_finsetSum
-- name    : BookProof.QgCouplingDGammaSum.creVec_finsetSum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:49.865358+00:00
-- url     : https://prove2.me/theorems/b35c025b-c68f-4543-8b0b-770c2026cea6
-- title:
--   `BookProof.QgCouplingDGammaSum.creVec_finsetSum` (s : Finset ι) (f : ι → (ℕ →₀ ℂ)) (x : FockAlg) : creVec (∑ i ∈ s, f i) x = ∑ i ∈ s, creVec (f i) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.creVec_finsetSum` (s : Finset ι) (f : ι → (ℕ →₀ ℂ)) (x : FockAlg) : creVec (∑ i ∈ s, f i) x = ∑ i ∈ s, creVec (f i) x
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.creVec_finsetSum`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creVec_finsetSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.creVec_finsetSum (s : Finset ι) (f : ι → (ℕ →₀ ℂ)) (x : FockAlg) :
    creVec (∑ i ∈ s, f i) x = ∑ i ∈ s, creVec (f i) x := by sorry
