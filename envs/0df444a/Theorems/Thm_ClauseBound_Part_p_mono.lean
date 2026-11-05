-- Prove2me | Theorems.Thm_ClauseBound_Part_p_mono
-- name    : ClauseBound.Part.p_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:36.061205+00:00
-- url     : https://prove2.me/theorems/8a9dac1f-4553-4f40-9cc7-94b00366bcb1
-- title:
--   Part: p mono
-- statement:
--   p is monotone.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Rec.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Rec.lean#L67-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions

theorem ClauseBound.Part.p_mono {E E' : ℕ} (h : E ≤ E') : p E ≤ p E' := by sorry
