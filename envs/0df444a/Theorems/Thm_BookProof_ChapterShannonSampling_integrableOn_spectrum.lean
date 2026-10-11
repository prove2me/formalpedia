-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_integrableOn_spectrum
-- name    : BookProof.ChapterShannonSampling.integrableOn_spectrum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:23:37.929001+00:00
-- url     : https://prove2.me/theorems/003ce77c-a009-497e-85ab-800c310417cd
-- title:
--   `BookProof.ChapterShannonSampling.integrableOn_spectrum` (F : Lp ℂ 2 (haarAddCircle (T := T))) : IntegrableOn (fun ξ : ℝ => (F : AddCircle T → ℂ) ξ) (Ioc (-(T / 2)) (-(T / 2) + T))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.integrableOn_spectrum` (F : Lp ℂ 2 (haarAddCircle (T := T))) : IntegrableOn (fun ξ : ℝ => (F : AddCircle T → ℂ) ξ) (Ioc (-(T / 2)) (-(T / 2) + T)) volume
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.integrableOn_spectrum`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.integrableOn_spectrum
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.integrableOn_spectrum (F : Lp ℂ 2 (haarAddCircle (T := T))) :
    IntegrableOn (fun ξ : ℝ => (F : AddCircle T → ℂ) ξ)
      (Ioc (-(T / 2)) (-(T / 2) + T)) volume := by sorry
