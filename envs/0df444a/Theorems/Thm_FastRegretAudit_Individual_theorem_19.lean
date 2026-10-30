-- Prove2me | Theorems.Thm_FastRegretAudit_Individual_theorem_19
-- name    : FastRegretAudit.Individual.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:34:36.846606+00:00
-- url     : https://prove2.me/theorems/014946ce-b888-48d1-9c7d-daa13c0fa4a7
-- title:
--   Theorem 19 — optimistic FTRL regret with both leader penalties
-- statement:
--   Let $d\ge1$, let $\Delta\subset\mathbb R^d$ be the probability simplex, and let $p,p_*$ be any primal norm and its coordinate dual. Let $\mathcal R$ obey the paper's midpoint 1-strong-convexity inequality for $p$, let $\eta>0$, and write $R=\sup_\Delta\mathcal R-\inf_\Delta\mathcal R\in[0,+\infty]$. Consider arbitrary real utility vectors $u^t$ and predictors $M^t$, an attaining OFTRL prefix $w^t$, and an attaining leader prefix $g^t$, both through $T\ge0$. For every mixed comparator $w^*\in\Delta$,
--
--   $$\sum_{t=1}^T\langle w^*-w^t,u^t\rangle\le\frac R\eta+\sum_{t=1}^T p_*(u^t-M^t)p(w^t-g^t)-\frac1{2\eta}\sum_{t=1}^T\bigl(p(w^t-g^t)^2+p(w^t-g^{t-1})^2\bigr).$$
--
--   Both negative terms are part of the statement. This is the auxiliary regret estimate underlying the one-step RVU bound; its leaders are actual maximizers rather than free vectors.
--
--   **Formalization Note** Regret and the two finite correction sums are real; the range term and final comparison are extended real. The zero-round leader minimizes the regularizer, and all regret sums start at round 1.
--
--   Differences from the source:
--   - encoding: finite nonempty strategy spaces → coordinates Fin d with 0 < d; reason: finite relabelling preserves every nonempty source simplex
--   - encoding: an arbitrary primal norm and its dual → a separating Mathlib seminorm and the coordinate unit-ball supremum; reason: represents every finite-dimensional norm without choosing the default primal norm
--   - encoding: argmin and argmax updates at the rounds used by the result → global optimality inequalities on the required finite prefixes; reason: expresses every attaining run without assuming unused future optimizers exist
--   - encoding: R is the exact supremum minus infimum with no separate finiteness assumption → EReal exact range and a bound in EReal with the other finite terms embedded; reason: agrees with the real formula for finite range and retains the infinite-range case without default real extrema
--   - generalization: §2 feedback from a fixed game with utilities in [0,1] → arbitrary real utility sequences without game-realizability or payoff bounds; reason: substituting the actual bounded game feedback recovers every source instance with the same constants and all conclusion clauses
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, Appendix C, supplementary p. 3, PDF p. 12, Theorem 19, Eq. (11)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Definitions.Def_FastRegretAudit_Individual_Runs
import Definitions.Def_FastRegretAudit_Individual_Geometry
import Definitions.Def_FastRegretAudit_Individual_Range

namespace FastRegretAudit.Individual

/-- Theorem 19, Appendix C, supplementary p. 3 (PDF 12), Eq. (11).
Arbitrary primal/dual norms; both negative terms; exact possibly infinite range. -/
theorem theorem_19 {d : ℕ} (hd : 0 < d) (p : PrimalNorm d)
    (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsMidpointStronglyConvex p.val 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (T : ℕ)
    (hw : IsOFTRLThrough 𝓡 η M u w T)
    (hg : IsLeaderThrough 𝓡 η u g T)
    (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ((∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t : ℝ) : EReal) ≤
      regularizerRange 𝓡 * ((η⁻¹ : ℝ) : EReal) +
        ((∑ t ∈ Finset.Icc 1 T, dualNorm p (u t - M t) * p.val (w t - g t)
          - 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T,
              ((p.val (w t - g t)) ^ 2 + (p.val (w t - g (t - 1))) ^ 2) : ℝ) : EReal) := by sorry

end FastRegretAudit.Individual
