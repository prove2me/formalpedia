-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_upsilon_bound
-- name    : ExtraConsensus.Sublinear.upsilon_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:04.499977+00:00
-- url     : https://prove2.me/theorems/9cdb8a9d-fb4e-41f5-8a7e-522d63529f35
-- title:
--   §3.2, proof of Theorem 3.5, p. 14 — there is υ > 0 with ‖(I − W̃)x‖²_W̃ = ‖x‖²_{(I−W̃)W̃(I−W̃)} ≤ υ‖x‖²_{W̃−W}
-- statement:
--   Under Assumption 1 there exists a constant $\upsilon>0$ such that for every stacked variable $\mathbf y\in\mathbb R^{n\times p}$
--   $$\|(I-\tilde W)\mathbf y\|_{\tilde W}^2=\|\mathbf y\|_{(I-\tilde W)\tilde W(I-\tilde W)}^2\le\upsilon\,\|\mathbf y\|_{\tilde W-W}^2 .$$
--
--   It lets the consensus residual absorb the term $\|(I-\tilde W)\mathbf x^k\|_{\tilde W}^2$ of (3.20), which is how (3.21) is obtained.
--
--   **Formalization Note** The page states the bound at the iterate $\mathbf x^k$ with a $\upsilon$ independent of $k$; the statement quantifies over every $\mathbf y$, which is what that independence means.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §3.2, proof of Theorem 3.5, p. 14 ("there exists a bounded υ > 0 …")

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- §3.2, proof of Theorem 3.5, p. 14. Under Assumption 1 there is a constant `υ > 0` such that
for every stacked `𝐲`, `‖(I − W̃)𝐲‖²_{W̃} = ‖𝐲‖²_{(I−W̃)W̃(I−W̃)} ≤ υ‖𝐲‖²_{W̃−W}`. -/
theorem upsilon_bound {n p : ℕ} (Gr : SimpleGraph (Fin n)) (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (hA1 : MixingAssumption Gr W Wt) :
    ∃ υ : ℝ, 0 < υ ∧ ∀ y : Stack n p,
      mnormSq Wt (mix (1 - Wt) y) = mnormSq ((1 - Wt) * Wt * (1 - Wt)) y ∧
        mnormSq Wt (mix (1 - Wt) y) ≤ υ * mnormSq (Wt - W) y := by sorry

end ExtraConsensus.Sublinear
