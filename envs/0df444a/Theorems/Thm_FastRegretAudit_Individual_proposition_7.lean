-- Prove2me | Theorems.Thm_FastRegretAudit_Individual_proposition_7
-- name    : FastRegretAudit.Individual.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:41.876876+00:00
-- url     : https://prove2.me/theorems/429c6a26-945b-44b3-928b-49dad05ac717
-- title:
--   Proposition 7 — exact numerical RVU inequality for one-step OFTRL
-- statement:
--   Let $d\ge1$, let $p,p_*$ be any primal/dual norm pair, and let $\mathcal R$ obey the paper's midpoint 1-strong-convexity condition on the simplex. Write $R=\sup_\Delta\mathcal R-\inf_\Delta\mathcal R\in[0,+\infty]$. For every $\eta>0$, arbitrary real utility sequence $u^0,u^1,\ldots$, every attaining OFTRL prefix through $T\ge0$ with predictor $M^t=u^{t-1}$, and every mixed comparator $w^*\in\Delta$,
--
--   $$\sum_{t=1}^T\langle w^*-w^t,u^t\rangle\le\frac R\eta+\eta\sum_{t=1}^T p_*(u^t-u^{t-1})^2-\frac1{4\eta}\sum_{t=1}^T p(w^t-w^{t-1})^2.$$
--
--   This retains the exact variation and negative movement coefficients. No leader, RVU guarantee, or stability estimate is assumed.
--
--   **Formalization Note** This is the numerical inequality called RVU in Proposition 7 and used with relaxed parameters in Theorem 11. Definition 3's narrower real-parameter class additionally requires $\alpha>0$ and $0<\beta\le\gamma$. With the printed constants it applies when $0<R<\infty$ and $\eta\le1/2$; neither restriction is imposed on this numerical inequality. In particular $\eta=1$ and zero range remain included.
--
--   Differences from the source:
--   - encoding: finite nonempty strategy spaces → coordinates Fin d with 0 < d; reason: finite relabelling preserves every nonempty source simplex
--   - encoding: an arbitrary primal norm and its dual → a separating Mathlib seminorm and the coordinate unit-ball supremum; reason: represents every finite-dimensional norm without choosing the default primal norm
--   - encoding: argmin and argmax updates at the rounds used by the result → global optimality inequalities on the required finite prefixes; reason: expresses every attaining run without assuming unused future optimizers exist
--   - encoding: R is the exact supremum minus infimum with no separate finiteness assumption → EReal exact range and a bound in EReal with the other finite terms embedded; reason: agrees with the real formula for finite range and retains the infinite-range case without default real extrema
--   - reading: Proposition 7 calls the guarantee RVU although Definition 3 restricts its parameters → the explicit numerical inequality for every positive stepsize; reason: Appendix C supplies this inequality without the class restrictions; the strict Definition 3 class is claimed only when its side conditions hold
--   - generalization: the game-level Proposition 7 uses the maximum range across players → the single-player bound uses that regularizer’s own exact range; reason: Appendix C gives the estimate for each regularizer; its range is bounded by the common maximum, recovering the entire printed guarantee
--   - generalization: §2 feedback from a fixed game with utilities in [0,1] → arbitrary real utility sequences without game-realizability or payoff bounds; reason: substituting the actual bounded game feedback recovers every source instance with the same constants and all conclusion clauses
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, main p. 5, §3.1.2, Proposition 7, PDF p. 5; proof Appendix C, supplementary pp. 2–5, PDF pp. 11–14

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Definitions.Def_FastRegretAudit_Individual_Runs
import Definitions.Def_FastRegretAudit_Individual_Geometry
import Definitions.Def_FastRegretAudit_Individual_Range

namespace FastRegretAudit.Individual

/-- Proposition 7, main p. 5; Appendix C, supplementary pp. 2–5.
The numerical RVU inequality holds for every positive stepsize. Definition 3's
additional class-parameter restrictions are not asserted for arbitrary η or range. -/
theorem proposition_7 {d : ℕ} (hd : 0 < d) (p : PrimalNorm d)
    (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsMidpointStronglyConvex p.val 𝓡)
    (u w : ℕ → Fin d → ℝ) (T : ℕ)
    (hw : IsOFTRLThrough 𝓡 η (fun t => u (t - 1)) u w T)
    (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ((∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t : ℝ) : EReal) ≤
      regularizerRange 𝓡 * ((η⁻¹ : ℝ) : EReal) +
        ((η * ∑ t ∈ Finset.Icc 1 T, (dualNorm p (u t - u (t - 1))) ^ 2
          - 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, (p.val (w t - w (t - 1))) ^ 2 : ℝ) : EReal) := by sorry

end FastRegretAudit.Individual
