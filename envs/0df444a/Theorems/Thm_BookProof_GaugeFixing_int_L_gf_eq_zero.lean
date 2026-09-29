-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_int_L_gf_eq_zero
-- name    : BookProof.GaugeFixing.int_L_gf_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:26:08.547421+00:00
-- url     : https://prove2.me/theorems/a175bbd3-6d20-40a4-8a48-754700339baf
-- title:
--   E.6.9.** The gauge-fixing Lagrangian has zero impact on physical observables: being BRST-exact, it integrates to zero
-- statement:
--   **E.6.9.** The gauge-fixing Lagrangian has zero impact on physical
--   observables: being BRST-exact, it integrates to zero.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.int_L_gf_eq_zero` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 218–221.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L218-L221

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.int_L_gf_eq_zero
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.int_L_gf_eq_zero (I : BrstIntegral S) : I.int (sTop S (Psi S)) = 0 := by sorry
