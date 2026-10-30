-- Prove2me | Theorems.Thm_DerivativeChainPrivate_northeast_root_continuation
-- name    : DerivativeChainPrivate.northeast_root_continuation
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:16:30.944774+00:00
-- url     : https://prove2.me/theorems/8d4c34e3-32d6-4745-a677-88931cd660e5
-- title:
--   Continuation of roots in a moving open northeast quadrant
-- statement:
--   For a fixed-degree monic polynomial family on a preconnected metric parameter space, assume joint evaluation continuity, a continuous moving quadrant corner, a uniform bound on all roots, and exclusion of roots on both northeast boundary rays. If one parameter has a root strictly northeast of the corner, every parameter does. The root bound, boundary exclusion and initial root are explicit assumptions.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/cube_continuation/Source/RootPersistence.lean#L99-L119

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.northeast_root_continuation {T : Type*} [MetricSpace T] [PreconnectedSpace T]
    (p : T → Polynomial ℂ) (n : ℕ) (hp : ∀ t, (p t).Monic)
    (hdeg : ∀ t, (p t).natDegree = n)
    (heval : Continuous (fun x : T × ℂ => (p x.1).eval x.2))
    (w : T → ℂ) (hw : Continuous w) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t z, (p t).eval z = 0 → ‖z‖ ≤ R)
    (hboundary : ∀ t z, (p t).eval z = 0 →
      ((z.re = (w t).re ∧ (w t).im ≤ z.im) ∨
        ((w t).re ≤ z.re ∧ z.im = (w t).im)) → False)
    (t₀ : T) (z₀ : ℂ) (hz₀ : (p t₀).eval z₀ = 0)
    (hr₀ : (w t₀).re < z₀.re) (hi₀ : (w t₀).im < z₀.im) :
    ∀ t, ∃ z : ℂ, (p t).eval z = 0 ∧ (w t).re < z.re ∧ (w t).im < z.im := by sorry
