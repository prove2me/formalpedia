-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionApproachLeft_formula_child_v1
-- name    : BraidsLinksMCG.extensionApproachLeft_formula_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:54:11.422205+00:00
-- url     : https://prove2.me/theorems/d921d87c-db77-4bce-9389-50dd2cafe602
-- title:
--   The left edge of the strand-extension approach path matches the standard approach
-- statement:
--   At the left edge of the strand-extension configuration square, the interpolating coordinate is exactly the standard approach path with the last old puncture shifted into the enlarged configuration.
-- source:
--   A theorem-only pointwise coordinate identity taken from the left-boundary equation extensionApproach_at_left in the strand-extension homotopy draft. The coordinate formula removes the draft-local path definitions and isolates this boundary obligation.

import Mathlib
import Definitions.Def_BraidsLinksMCG_StandardLoops

theorem BraidsLinksMCG.extensionApproachLeft_formula_child_v1 (n : ℕ) (j : Fin n) (u : Set.Icc (0 : ℝ) 1) :
    ((1 - (u : ℝ) : ℝ) : ℂ) * (((n : ℝ) + 2 : ℝ) : ℂ) +
      ((u : ℝ) : ℂ) * ((((j : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) +
      (((u : ℝ) * (1 - (u : ℝ)) : ℝ) : ℂ) * Complex.I =
      BraidsLinksMCG.approachFun (n + 1) j.castSucc (u : ℝ) := by sorry
