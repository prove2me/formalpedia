-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_shift_domain_of_convex_chord
-- name    : AvramDividend.Classical.esscher_shift_domain_of_convex_chord
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:38:11.968585+00:00
-- url     : https://prove2.me/theorems/8de4662a-f029-40d5-8ebc-2ae779cad233
-- title:
--   Esscher shift domain from a convexity chord at the root
-- statement:
--   For a real function psi with a positive root value q at phi and zero at zero, the convexity chord inequality at phi with weights phi/(phi+theta) and theta/(phi+theta) forces psi at phi+theta to exceed q. This discharges the exact domain premise needed to apply the scale-function Laplace clause at theta+phi in the unbounded Esscher root decay route.
-- source:
--   Isolates the exact domain side-condition of parent AvramDividend.Classical.unbounded_esscher_root_first_passage_scale_decay (680362b2): the dossier derives q < X.psi (phi+theta) from convexity of X.psi, psi 0 = 0, and the chord inequality. The child takes no process, scale-function, or Open theorem premises, only real hypotheses, so the decomposition is acyclic and independently provable by elementary real arithmetic.

import Mathlib

theorem AvramDividend.Classical.esscher_shift_domain_of_convex_chord
    (ψ : ℝ → ℝ) (q φ θ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hroot : ψ φ = q) (hzero : ψ 0 = 0)
    (hchord : ψ φ ≤ (φ / (φ + θ)) * ψ (φ + θ) + (θ / (φ + θ)) * ψ 0) :
    q < ψ (φ + θ) := by sorry
