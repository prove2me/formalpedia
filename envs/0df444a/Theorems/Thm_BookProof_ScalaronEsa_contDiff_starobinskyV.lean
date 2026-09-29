-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
-- name    : BookProof.ScalaronEsa.contDiff_starobinskyV
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:37:04.410265+00:00
-- url     : https://prove2.me/theorems/45df48ff-f419-4353-a7f9-a3d835b13dab
-- title:
--   The Lean 4 theorem `contDiff_starobinskyV` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `contDiff_starobinskyV` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.contDiff_starobinskyV
--
-- This node exists because `Definitions/Def_ChapterScalaronFiberFL.lean` needs the smoothness of
-- the Einstein-frame scalaron potential as a *Proved* platform theorem: a Definitions module may
-- import a Theorems module, but only once that theorem is Proved.  The declaration is hollowed out
-- of the definitions layer (`Def_ChapterScalaronCoreEsa` documents it and does not declare it), so
-- it has to live in the theorem layer.
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.Starobinsky


open Filter Topology


noncomputable section

theorem BookProof.ScalaronEsa.contDiff_starobinskyV (M alpha : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun phi : ℝ => starobinskyV M alpha phi) := by sorry
