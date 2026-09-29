-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_Pm_mul_Vm
-- name    : BookProof.GaugeFixing.Pm_mul_Vm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:23:03.25139+00:00
-- url     : https://prove2.me/theorems/96e530ca-3ca0-40f5-845e-5dd01e2f7f04
-- title:
--   Action of the gauge-fixing projection on the vacuum
-- statement:
--   Action of the gauge-fixing projection on the vacuum.
--
--   In the $2\times2$ matrix model the projection matrix $P_m$ annihilates onto the vacuum while $V_m$ creates it; they satisfy
--   $$
--   P_m\,V_m = P_m.
--   $$
--
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.Pm_mul_Vm` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 266–267.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L266-L267

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.Pm_mul_Vm
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.Pm_mul_Vm : Pm * Vm = Pm := by sorry
