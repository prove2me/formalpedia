-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_integrable_bdd_mul
-- name    : BookProof.ChapterSphericalPlancherel.integrable_bdd_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:22:03.620753+00:00
-- url     : https://prove2.me/theorems/6ce21402-d5ec-45b4-b67a-00985f223b18
-- title:
--   `BookProof.ChapterSphericalPlancherel.integrable_bdd_mul` (G : ℝ → ℂ) (hG : Integrable G) (u : ℝ → ℝ) (hu : Continuous u) (hb : ∀ x, |u x| ≤ 1) : Integrable (fun x : ℝ => (u x : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.integrable_bdd_mul` (G : ℝ → ℂ) (hG : Integrable G) (u : ℝ → ℝ) (hu : Continuous u) (hb : ∀ x, |u x| ≤ 1) : Integrable (fun x : ℝ => (u x : ℂ) * G x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.integrable_bdd_mul`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.integrable_bdd_mul
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.integrable_bdd_mul (G : ℝ → ℂ) (hG : Integrable G) (u : ℝ → ℝ) (hu : Continuous u)
    (hb : ∀ x, |u x| ≤ 1) : Integrable (fun x : ℝ => (u x : ℂ) * G x) := by sorry
