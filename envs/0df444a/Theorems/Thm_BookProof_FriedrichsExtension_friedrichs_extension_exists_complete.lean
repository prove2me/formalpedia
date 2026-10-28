-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists_complete
-- name    : BookProof.FriedrichsExtension.friedrichs_extension_exists_complete
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T12:23:53.926826+00:00
-- url     : https://prove2.me/theorems/213da18d-043c-4c3e-8344-94d6b5bc7b13
-- title:
--   The Lean 4 theorem `friedrichs_extension_exists_complete` (Friedrichs extension, with the completeness hypothesis the original node lacks) in the `ChapterFriedrichsExtension` chapter of the...
-- statement:
--   The Lean 4 theorem `friedrichs_extension_exists_complete` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization: every densely defined symmetric positive operator on a **complete** complex inner product space has a positive self-adjoint extension. Corrected restatement of the disproved `friedrichs_extension_exists`, whose published preamble omitted `variable [CompleteSpace F]`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.friedrichs_extension_exists_complete
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp

/-! **Why this statement exists (2026-10-27).**  The original
`BookProof.FriedrichsExtension.friedrichs_extension_exists` was published from a
stub whose preamble omitted `variable [CompleteSpace F]`, so the platform's
target reads

  `∀ (P : PosSymOp F), Dense (P.dom : Set F) → ∃ Dom A, …` over an *arbitrary*
  (possibly incomplete) normed space,

which is false — the Friedrichs construction completes the form domain inside
`F`, and completeness of `F` is what makes the extension land in `F`.  The node
carries an **ACCEPTED disproof** (submission `b9369169`, 2026-10-05, `c₀₀` +
discontinuous `Σ xₙ`), so it is permanently `Disproved` and no proof of it can
ever be accepted; the statement text itself is immutable on the platform
(`PATCH` edits NL/source/tags only, `submit-problem` answers *already exists*).

This node is the same proposition **with the hypothesis it actually needs**, so
the four bundles that need a positive self-adjoint extension
(`ChapterFermionFock`, `ChapterNavierStokesFullEulerianFock`,
`ChapterYangMillsFockFriedrichs`, `ChapterNavierStokesFullLagrangianFock`) can
cite a statement that can be proved instead of one that has been disproved. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable [CompleteSpace F]

theorem BookProof.FriedrichsExtension.friedrichs_extension_exists_complete (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension P.op A := by sorry
