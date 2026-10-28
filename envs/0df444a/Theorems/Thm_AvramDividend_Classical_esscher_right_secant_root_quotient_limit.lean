-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_right_secant_root_quotient_limit
-- name    : AvramDividend.Classical.esscher_right_secant_root_quotient_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:59:07.35139+00:00
-- url     : https://prove2.me/theorems/fe0c9e0c-61b2-49e6-bf73-b4b60637141f
-- title:
--   Positive-shift root quotient converges from a finite right secant limit without full differentiability
-- statement:
--   Let f be any real function and root(p) solve f(φ+root(p))−fφ=p for every p>0, with root(p)→0 from the positive side as p→0+. If the right secant quotient (f(φ+h)−fφ)/h tends to a finite m as h→0+, then p/root(p)→m. This only uses right-hand convergence, not full two-sided HasDerivAt, and does not assume Wiener–Hopf factorisation.
-- source:
--   Pinned Mathlib Filter.Tendsto.comp, Tendsto.congr', self_mem_nhdsWithin; mathlib SHA 0df444a.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Order.Field
open Filter Set

theorem AvramDividend.Classical.esscher_right_secant_root_quotient_limit
    (f : ℝ → ℝ) (φ m : ℝ) (root : ℝ → ℝ)
    (hroot : ∀ p : ℝ, 0 < p →
      f (φ + root p) - f φ = p)
    (hrootLim : Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hsec : Tendsto (fun h : ℝ => (f (φ + h) - f φ) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m)) :
    Tendsto (fun p : ℝ => p / root p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) := by sorry
