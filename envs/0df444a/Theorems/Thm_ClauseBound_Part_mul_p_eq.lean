-- Prove2me | Theorems.Thm_ClauseBound_Part_mul_p_eq
-- name    : ClauseBound.Part.mul_p_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:35:33.903927+00:00
-- url     : https://prove2.me/theorems/fa44ac2a-6f8c-4d7a-a1b3-c2c40b4e1980
-- title:
--   Part: mul p eq
-- statement:
--   E·p(E) = Σ_{v ≥ 1} Σ_{k ≥ 1, kv ≤ E} v·p(E − kv).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Rec.lean#L74-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Rec.lean#L74-L102

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

theorem ClauseBound.Part.mul_p_eq (E : ℕ) : E * p E = ∑ v ∈ Icc 1 E, ∑ k ∈ Icc 1 (E / v), v * p (E - k * v) := by sorry
