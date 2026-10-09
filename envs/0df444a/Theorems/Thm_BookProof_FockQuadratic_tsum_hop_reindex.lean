-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_tsum_hop_reindex
-- name    : BookProof.FockQuadratic.tsum_hop_reindex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T20:35:32.608668+00:00
-- url     : https://prove2.me/theorems/4dacb350-f059-4978-9d80-f01ff6127a3b
-- title:
--   `BookProof.FockQuadratic.tsum_hop_reindex` {P Q : Idx ι} {F G : Idx ι → ℂ} (hF : ∀ a, ¬ P ≤ a → F a = 0) (hG : ∀ b, ¬ Q ≤ b → G b = 0) (hEq : ∀ a, P ≤ a → F a = G (tgt P...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.tsum_hop_reindex` {P Q : Idx ι} {F G : Idx ι → ℂ} (hF : ∀ a, ¬ P ≤ a → F a = 0) (hG : ∀ b, ¬ Q ≤ b → G b = 0) (hEq : ∀ a, P ≤ a → F a = G (tgt P Q a)) : ∑' a, F a = ∑' b, G b
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.tsum_hop_reindex`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.tsum_hop_reindex
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.FockQuadratic


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

theorem BookProof.FockQuadratic.tsum_hop_reindex {P Q : Idx ι} {F G : Idx ι → ℂ}
    (hF : ∀ a, ¬ P ≤ a → F a = 0) (hG : ∀ b, ¬ Q ≤ b → G b = 0)
    (hEq : ∀ a, P ≤ a → F a = G (tgt P Q a)) : ∑' a, F a = ∑' b, G b := by sorry
