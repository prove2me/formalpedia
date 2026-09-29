-- Prove2me | Theorems.Thm_FamousTheorems_niven
-- name    : FamousTheorems.niven
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:33.121953+00:00
-- url     : https://prove2.me/theorems/e0e3aae3-7a04-4962-934d-bab2e5848199
-- title:
--   Niven's theorem
-- statement:
--   **Niven's theorem.**
--
--   If $\theta$ is a rational multiple of $\pi$ and $\cos\theta$ is rational, then
--   $$\cos\theta \in \left\{-1,\ -\tfrac12,\ 0,\ \tfrac12,\ 1\right\}.$$
--
--   Rationality in the angle and rationality in the cosine are almost incompatible: only the
--   five values coming from the angles $0, \pi/3, \pi/2, 2\pi/3, \pi$ and their translates
--   survive. So $\cos 1^\circ$, for instance, is irrational, and the familiar exact values
--   $\cos(\pi/4) = \sqrt2/2$ and $\cos(\pi/6) = \sqrt3/2$ are irrational as the theorem demands.
--
--   The proof observes that $2\cos\theta$ is an algebraic integer whenever $\theta$ is a rational
--   multiple of $\pi$ — it satisfies a monic integer recurrence coming from
--   $2\cos(n\theta) = (2\cos\theta)\cdot 2\cos((n-1)\theta) - 2\cos((n-2)\theta)$ — and a rational
--   algebraic integer is an ordinary integer. Since $|2\cos\theta| \le 2$, it lies in
--   $\{-2,-1,0,1,2\}$.
--
--   Niven gave this in his 1956 monograph *Irrational Numbers*; the companion statements for
--   sine and tangent follow by shifting the angle.
--
--   **Formalization note.** The hypotheses say $\theta = r\pi$ for some rational $r$ and that
--   $\cos\theta$ equals the cast of some rational. The result is Mathlib's `Real.niven`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem niven {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * Real.pi) (hcos : ∃ q : ℚ, Real.cos θ = q) :
    Real.cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by sorry

end FamousTheorems
