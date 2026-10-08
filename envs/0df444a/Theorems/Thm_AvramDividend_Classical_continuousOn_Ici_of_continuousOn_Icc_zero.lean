-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_Ici_of_continuousOn_Icc_zero
-- name    : AvramDividend.Classical.continuousOn_Ici_of_continuousOn_Icc_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:21:27.013072+00:00
-- url     : https://prove2.me/theorems/6afc82f6-7dcb-4cd3-b9b4-6718dcb17c23
-- title:
--   Continuity on every finite interval [0,B] implies continuity on the nonnegative ray
-- statement:
--   A real function that is continuous on every compact nonnegative interval [0,B] is continuous on the whole nonnegative ray [0,∞). For each point x≥0, the relatively open neighbourhood [0,∞)∩(-∞,x+1) lies in [0,x+1], so pinned Mathlib continuousOn_of_locally_continuousOn closes the global property. This is the exact topological glue that promotes local dominated continuity of the Lévy exponent to the global continuity assumed by the already Proved positive-Esscher-root theorem.
-- source:
--   Pinned Mathlib continuousOn_of_locally_continuousOn; source-neutral topology.

import Mathlib
open Set

theorem AvramDividend.Classical.continuousOn_Ici_of_continuousOn_Icc_zero
    (f : ℝ → ℝ)
    (hcompact : ∀ B : ℝ, 0 ≤ B → ContinuousOn f (Icc (0 : ℝ) B)) :
    ContinuousOn f (Ici (0 : ℝ)) := by sorry
