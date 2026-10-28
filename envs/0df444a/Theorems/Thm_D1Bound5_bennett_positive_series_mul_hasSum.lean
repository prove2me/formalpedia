-- Prove2me | Theorems.Thm_D1Bound5_bennett_positive_series_mul_hasSum
-- name    : D1Bound5.bennett_positive_series_mul_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:34.978893+00:00
-- url     : https://prove2.me/theorems/f108c390-fcc4-4ef9-a426-85eb71065226
-- title:
--   Bennett positive series mul has Sum
-- statement:
--   Weighted Cauchy multiplication for positive real power series. The two series are actually summable at the chosen radius; no formal evaluation is silently treated as an analytic sum.
-- source:
--   D1Bound5/BennettPositiveSeries.lean, lines 105-138, SHA-256 97c8e1703cfe77445d9777396cd5b2920aa185f7c75649ef58d66b03bb6b026f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
open Finset

namespace D1Bound5
















theorem _root_.D1Bound5.bennett_positive_series_mul_hasSum
    (P Q : PowerSeries ℝ) (r s t : ℝ) (hr : 0 ≤ r)
    (hP : ∀ n, 0 ≤ PowerSeries.coeff n P)
    (hQ : ∀ n, 0 ≤ PowerSeries.coeff n Q)
    (hs : HasSum (fun n : ℕ => PowerSeries.coeff n P * r^n) s)
    (ht : HasSum (fun n : ℕ => PowerSeries.coeff n Q * r^n) t) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (P*Q) * r^n) (s*t) := by sorry





end D1Bound5
end
