-- Prove2me | Theorems.Thm_BookProof_DampedOscillatorEnergy_hasDerivAt_dampedEnergy
-- name    : BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:25:27.348872+00:00
-- url     : https://prove2.me/theorems/9dc70499-4951-4235-bdde-1be52221c7db
-- title:
--   `BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy` {lam omega : ℝ} {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t) (heq : ∀ t, a t + lam *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDampedOscillatorEnergy`.
--
--   `BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy` {lam omega : ℝ} {x v a : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t) (heq : ∀ t, a t + lam * v t + omega ^ 2 * x t = 0) (t : ℝ) : HasDerivAt (dampedEnergy omega x v) (-(lam * v t ^ 2)) t
--
--   Formalization note: Lean 4 identifier `BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy`.

-- Generated from ChapterDampedOscillatorEnergy.lean — theorem BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy



open MeasureTheory

theorem BookProof.DampedOscillatorEnergy.hasDerivAt_dampedEnergy {lam omega : ℝ} {x v a : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, a t + lam * v t + omega ^ 2 * x t = 0) (t : ℝ) :
    HasDerivAt (dampedEnergy omega x v) (-(lam * v t ^ 2)) t := by sorry
