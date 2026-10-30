-- Prove2me | Theorems.Thm_FastRegretAudit_Individual_lemma_20
-- name    : FastRegretAudit.Individual.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:09.088679+00:00
-- url     : https://prove2.me/theorems/7ab98446-47c2-4a3f-aa2d-44157bf23e04
-- title:
--   Lemma 20 (Stability) — both primal/dual estimates
-- statement:
--   Let $d\ge1$, let $p,p_*$ be any primal/dual norm pair on $\mathbb R^d$, and let $\mathcal R$ satisfy the paper's midpoint 1-strong-convexity condition for $p$ on the simplex. Fix $\eta>0$, arbitrary utility and predictor sequences $u^t,M^t$, an OFTRL prefix through $T+1$, and a leader prefix through $T$, with $T\ge0$. Then both estimates hold:
--
--   $$p(w^t-g^t)\le\eta p_*(M^t-u^t)\quad(1\le t\le T),\qquad p(g^t-w^{t+1})\le\eta p_*(M^{t+1})\quad(0\le t\le T).$$
--
--   The second inequality includes the initial movement from the zero-round leader to the first play. These bounds apply to arbitrary predictors; neither is replaced by the later derived bound on consecutive plays.
--
--   **Formalization Note** At round 0 the two regularizer minimizers coincide by midpoint strict convexity, so the omitted zero-round version of the first inequality is automatic. No regularizer range, continuity, or differentiability assumption is used.
--
--   Differences from the source:
--   - encoding: finite nonempty strategy spaces → coordinates Fin d with 0 < d; reason: finite relabelling preserves every nonempty source simplex
--   - encoding: an arbitrary primal norm and its dual → a separating Mathlib seminorm and the coordinate unit-ball supremum; reason: represents every finite-dimensional norm without choosing the default primal norm
--   - encoding: argmin and argmax updates at the rounds used by the result → global optimality inequalities on the required finite prefixes; reason: expresses every attaining run without assuming unused future optimizers exist
--   - encoding: the displayed update estimates use positive rounds and the initial minimizers → the first estimate is indexed by 1 ≤ t ≤ T and the second by 0 ≤ t ≤ T; reason: retains both update domains and the initial movement; the first estimate at zero is automatic because w⁰ and g⁰ are the same minimizer
--   - generalization: §2 feedback from a fixed game with utilities in [0,1] → arbitrary real utility sequences without game-realizability or payoff bounds; reason: substituting the actual bounded game feedback recovers every source instance with the same constants and all conclusion clauses
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, Appendix C, supplementary pp. 4–5, PDF pp. 13–14, Lemma 20, Eqs. (14)–(15)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting
import Definitions.Def_FastRegretAudit_Individual_Runs
import Definitions.Def_FastRegretAudit_Individual_Geometry

namespace FastRegretAudit.Individual

/-- Lemma 20, Appendix C, supplementary pp. 4–5 (PDF 13–14).
Both (14) and (15) are retained. At t = 0 only (15) is claimed; (14)
compares actual positive-round OFTRL iterates with their leaders. -/
theorem lemma_20 {d : ℕ} (hd : 0 < d) (p : PrimalNorm d)
    (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsMidpointStronglyConvex p.val 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (T : ℕ)
    (hw : IsOFTRLThrough 𝓡 η M u w (T + 1))
    (hg : IsLeaderThrough 𝓡 η u g T) :
    (∀ t : ℕ, 1 ≤ t → t ≤ T → p.val (w t - g t) ≤ η * dualNorm p (M t - u t)) ∧
      (∀ t : ℕ, t ≤ T → p.val (g t - w (t + 1)) ≤ η * dualNorm p (M (t + 1))) := by sorry

end FastRegretAudit.Individual
