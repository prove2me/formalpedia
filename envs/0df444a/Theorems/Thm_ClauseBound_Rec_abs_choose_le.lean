-- Prove2me | Theorems.Thm_ClauseBound_Rec_abs_choose_le
-- name    : ClauseBound.Rec.abs_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:26.993327+00:00
-- url     : https://prove2.me/theorems/04571e1e-740e-4160-ba76-aed0e66b9326
-- title:
--   Rec: abs choose le
-- statement:
--   |C(a, k)| ≤ 2^(|a| + k).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Window.lean#L42-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Window.lean#L42-L53

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
import Definitions.Def_PiecesStatement
import Definitions.Def_ClauseBound_Rec_Window
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset

theorem ClauseBound.Rec.abs_choose_le (a : ℤ) (k : ℕ) : |Ring.choose a k| ≤ 2 ^ (a.natAbs + k) := by sorry
