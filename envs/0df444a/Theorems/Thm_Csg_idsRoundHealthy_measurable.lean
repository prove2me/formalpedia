-- Prove2me | Theorems.Thm_Csg_idsRoundHealthy_measurable
-- name    : Csg.idsRoundHealthy_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:51:33.148022+00:00
-- url     : https://prove2.me/theorems/435302bb-70f1-4184-9d48-6b4c5e05fece
-- title:
--   Csg: ids Round Healthy measurable
-- statement:
--   The Csg construction uses the ids Round Healthy measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L160-L161
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L160-L161

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)

theorem Csg.idsRoundHealthy_measurable : Measurable idsRoundHealthy := by sorry
