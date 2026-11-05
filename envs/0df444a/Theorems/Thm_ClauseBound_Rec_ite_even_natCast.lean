-- Prove2me | Theorems.Thm_ClauseBound_Rec_ite_even_natCast
-- name    : ClauseBound.Rec.ite_even_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:23.768269+00:00
-- url     : https://prove2.me/theorems/7641f8d8-7221-4289-9131-8549a9e9ee95
-- title:
--   Rec: ite even nat Cast
-- statement:
--   The sign written with a case distinction is the power of −1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Window.lean#L36-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Window.lean#L36-L39

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

theorem ClauseBound.Rec.ite_even_natCast (j : ℕ) : (if Even (j : ℤ) then (1 : ℤ) else -1) = (-1) ^ j := by sorry
