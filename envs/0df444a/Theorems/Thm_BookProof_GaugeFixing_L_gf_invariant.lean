-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_L_gf_invariant
-- name    : BookProof.GaugeFixing.L_gf_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:22:08.572508+00:00
-- url     : https://prove2.me/theorems/15a06225-9b05-4cf5-b236-27afd2b9b39b
-- title:
--   E.6.8.** The gauge-fixing Lagrangian is BRST-invariant: `s (s Ψ) = 0`
-- statement:
--   **E.6.8.** The gauge-fixing Lagrangian is BRST-invariant: `s (s Ψ) = 0`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.L_gf_invariant` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 200–202.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L200-L202

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.L_gf_invariant
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.L_gf_invariant : S.s (S.s (Psi S)) = S.zero (2, 1) := by sorry
