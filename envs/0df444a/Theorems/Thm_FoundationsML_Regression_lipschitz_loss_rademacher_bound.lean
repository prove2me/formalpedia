-- Prove2me | Theorems.Thm_FoundationsML_Regression_lipschitz_loss_rademacher_bound
-- name    : FoundationsML.Regression.lipschitz_loss_rademacher_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:09:36.31546+00:00
-- url     : https://prove2.me/theorems/0a7e59e8-ff8e-40c8-b54a-5c9a8f0024c5
-- title:
--   Proposition 11.2 — Rademacher complexity of µ-Lipschitz loss functions
-- statement:
--   **Statement (Proposition 11.2, p. 269, PDF p. 286).** Let $L$ be non-negative, bounded by
--   $M>0$, and $\mu$-Lipschitz in its first argument. Then, for any sample $S$,
--   $\hat R_S(G) \le \mu\hat R_S(H)$, where $G$ is the loss-composed family associated to $H$.
--   The Talagrand's-contraction-lemma step (chunk `05-svm`'s Lemma 5.7) that the goal's proof
--   reuses.
--
--   **Formalization Note.** `hLlip` states Lipschitzness *in the first argument only*
--   (`∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ|y1-y2|`), matching `BRIEF.md`'s pitfall note exactly
--   — `y'` (the true label) is universally quantified outside the Lipschitz inequality, `y1,y2`
--   (candidate predictions) are the two points compared.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 269, Proposition 11.2 (PDF p. 286)

import Mathlib
import Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_Regression_LossComposedFamily

namespace FoundationsML.Regression

/-- Proposition 11.2 (Rademacher complexity of µ-Lipschitz loss functions; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 269,
PDF p. 286). Let `L` be a non-negative loss bounded by `M > 0` that is `µ`-Lipschitz in its
first argument. Then, for any sample `S`, the Rademacher complexity of the loss-composed
family `G = {(x,y) ↦ L(h(x),y) : h ∈ H}` satisfies `R̂_S(G) ≤ µ R̂_S(H)`. -/
theorem lipschitz_loss_rademacher_bound
    {X : Type*} {m : ℕ}
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (H : Set (X → ℝ)) (S : Fin m → X × ℝ) :
    EmpiricalRademacherComplexity (LossComposedFamily L H) S ≤
      μ * EmpiricalRademacherComplexity H (fun i => (S i).1) := by sorry

end FoundationsML.Regression
