-- Prove2me | Theorems.Thm_FamousTheorems_bohr_mollerup_theorem
-- name    : FamousTheorems.bohr_mollerup_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:48.929375+00:00
-- url     : https://prove2.me/theorems/a25f8a69-d9b7-4a3d-82a0-88ea3166d8c3
-- title:
--   The Bohr–Mollerup theorem
-- statement:
--   **The Bohr–Mollerup theorem.** Let $f:(0,\infty)\to(0,\infty)$ satisfy
--   1. $f(1)=1$,
--   2. $f(x+1)=x\,f(x)$ for all $x>0$,
--   3. $\log f$ is convex on $(0,\infty)$.
--
--   Then $f=\Gamma$ on $(0,\infty)$.
--
--   Among all functions interpolating the factorial, the Gamma function is thus the unique log-convex one. Artin made this characterization the foundation of his treatment of the Gamma function, and it gives quick proofs of identities such as the duplication formula.
--
--   **Formalization note.** Mathlib's `Real.eq_Gamma_of_log_convex`. `f` is a function `ℝ → ℝ`, and all hypotheses and the conclusion `Set.EqOn f Real.Gamma (Set.Ioi 0)` concern positive arguments only.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.eq_Gamma_of_log_convex`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bohr_mollerup_theorem {f : ℝ → ℝ} (hf_conv : ConvexOn ℝ (Set.Ioi 0) (Real.log ∘ f)) (hf_feq : ∀ {y : ℝ}, 0 < y → f (y + 1) = y * f y)
    (hf_pos : ∀ {y : ℝ}, 0 < y → 0 < f y) (hf_one : f 1 = 1) : Set.EqOn f Real.Gamma (Set.Ioi 0) := by sorry

end FamousTheorems
