-- Prove2me | Theorems.Thm_FamousTheorems_lebesgue_monotone_differentiation_6b
-- name    : FamousTheorems.lebesgue_monotone_differentiation_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:52.13018+00:00
-- url     : https://prove2.me/theorems/ab8a0b4a-b97b-43a7-b9fc-ee3db2860240
-- title:
--   Lebesgue's theorem: monotone functions are differentiable almost everywhere
-- statement:
--   **Lebesgue's theorem: monotone functions are differentiable almost everywhere.** Let $f:\mathbb R\to\mathbb R$ be monotone. Then $f$ is differentiable at Lebesgue-almost every point of $\mathbb R$.
--
--   This is the central result of Lebesgue's theory of differentiation. It implies that functions of bounded variation and Lipschitz functions of one variable are differentiable almost everywhere. It leads to the fundamental theorem of calculus for the Lebesgue integral, and it contrasts with the existence of continuous nowhere-differentiable functions.
--
--   **Formalization note.** Mathlib's `Monotone.ae_differentiableAt`. `∀ᵐ x ∂volume, P x` means that $P$ holds outside a Lebesgue null set.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Monotone.ae_differentiableAt`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem lebesgue_monotone_differentiation_6b {f : ℝ → ℝ} (hf : Monotone f) : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by sorry

end FamousTheorems
