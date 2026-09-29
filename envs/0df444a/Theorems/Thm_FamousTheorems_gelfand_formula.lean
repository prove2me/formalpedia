-- Prove2me | Theorems.Thm_FamousTheorems_gelfand_formula
-- name    : FamousTheorems.gelfand_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:57.113273+00:00
-- url     : https://prove2.me/theorems/bf0ea18b-1e56-4765-b6a4-885ce4d21eef
-- title:
--   Gelfand's formula for the spectral radius
-- statement:
--   **Gelfand's formula.** Let $A$ be a complex Banach algebra and $a\in A$. Then
--   $$\lim_{n\to\infty}\|a^n\|^{1/n}=\rho(a),$$
--   where $\rho(a)=\sup\{|\lambda|:\lambda\in\sigma(a)\}$ is the spectral radius of $a$.
--
--   The formula links the purely algebraic spectrum to the norm. It shows that the spectral radius does not depend on the choice of equivalent norm, and that $\rho(a)\le\|a\|$ with equality for normal elements of a C*-algebra. It is basic in spectral theory, in the study of iterative methods ($a^n\to0$ exactly when $\rho(a)<1$), and in the theory of C*-algebras.
--
--   **Formalization note.** Mathlib's `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`. `spectralRadius ℂ a` takes values in `ENNReal`, so the sequence $\|a^n\|^{1/n}$ is mapped into `ENNReal` by `ENNReal.ofReal`. The power `1 / (n : ℝ)` is a real power.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gelfand_formula {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (a : A) :
    Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ)))) Filter.atTop
      (nhds (spectralRadius ℂ a)) := by sorry

end FamousTheorems
