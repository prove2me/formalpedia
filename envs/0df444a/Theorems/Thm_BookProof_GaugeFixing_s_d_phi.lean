-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_s_d_phi
-- name    : BookProof.GaugeFixing.s_d_phi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:29:18.158962+00:00
-- url     : https://prove2.me/theorems/7d77bcb6-1d44-4254-b6db-05d08cd4560f
-- title:
--   `s (dφ) = d (s φ) = 0`: the exterior derivative of a BRST-invariant scalar is BRST-invariant
-- statement:
--   `s (dφ) = d (s φ) = 0`: the exterior derivative of a BRST-invariant scalar is
--   BRST-invariant.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.s_d_phi` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 171–176.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L171-L176

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.s_d_phi
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.s_d_phi : S.s (S.d S.phi) = S.zero (1, 1) := by sorry
