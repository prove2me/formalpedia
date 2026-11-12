-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_independent_pair_measurable_image_law_20261111
-- name    : AvramDividend.Classical.avram_a06_independent_pair_measurable_image_law_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:12:43.927413+00:00
-- url     : https://prove2.me/theorems/b5a0ee20-9b14-43bd-a43b-871a9a5cfd17
-- title:
--   A measurable image of independent streams has the pushforward product law
-- statement:
--   Two independent measurable random streams have a joint law equal to the product of their marginal laws. Applying any measurable function to the pair therefore has the same law as applying it to independently sampled inputs. This is a direct measure-valued bridge for the A06 random-grid marked-sum process.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_a06_independent_pair_measurable_image_law_20261111
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B) (Z : A × B → C)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) :
    Measure.map (fun ω => Z (X ω, Y ω)) P =
      Measure.map Z ((Measure.map X P).prod (Measure.map Y P)) := by sorry
