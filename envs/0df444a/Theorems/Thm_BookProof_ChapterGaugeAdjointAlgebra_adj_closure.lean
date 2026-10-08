-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_adj_closure
-- name    : BookProof.ChapterGaugeAdjointAlgebra.adj_closure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:51:55.207411+00:00
-- url     : https://prove2.me/theorems/825e2899-4378-46da-aff1-eccac6cc67c6
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.adj_closure` (θ η X : L) : adjVar η (adjVar θ X) - adjVar θ (adjVar η X) = adjVar ⁅θ, η⁆ X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.adj_closure` (θ η X : L) : adjVar η (adjVar θ X) - adjVar θ (adjVar η X) = adjVar ⁅θ, η⁆ X
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.adj_closure`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.adj_closure
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.adj_closure (θ η X : L) :
    adjVar η (adjVar θ X) - adjVar θ (adjVar η X) = adjVar ⁅θ, η⁆ X := by sorry
