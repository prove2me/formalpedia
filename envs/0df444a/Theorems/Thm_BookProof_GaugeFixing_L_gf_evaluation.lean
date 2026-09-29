-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_L_gf_evaluation
-- name    : BookProof.GaugeFixing.L_gf_evaluation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:08:29.277848+00:00
-- url     : https://prove2.me/theorems/84614569-2e9b-4892-81cc-84e4658500ec
-- title:
--   E.6.7 (the culminating theorem).** BRST exactness generates the gauge-fixing Lagrangian: `s Ψ = B · (v − dφ) − c̄ · c`
-- statement:
--   **E.6.7 (the culminating theorem).** BRST exactness generates the
--   gauge-fixing Lagrangian:
--
--   `s Ψ = B · (v − dφ) − c̄ · c`.
--
--   The first term is the Lagrange multiplier enforcing `v = dφ` (the delta function
--   `δ(v − dφ)` in the path integral); the second is a ghost term with no momentum
--   dependence, so the ghosts decouple.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.L_gf_evaluation` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 184–198.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L184-L198

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.L_gf_evaluation
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.L_gf_evaluation :
    S.s (Psi S) =
      S.sub (2, 0) (S.mul (1, 0) (1, 0) S.B (gaugeField S))
        (S.mul (1, -1) (1, 1) S.c_bar S.c) := by sorry
