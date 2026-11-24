-- Prove2me | Theorems.Thm_Arxiv0812_1178_alpha_minimization_separates
-- name    : Arxiv0812_1178.alpha_minimization_separates
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:53:25.628141+00:00
-- url     : https://prove2.me/theorems/79aec7ae-449f-48c8-a608-09103c8963aa
-- title:
--   Sec. 4.B, 'Minimization w.r.t. $\alpha$': the minimization over $\alpha$ separates by instant
-- statement:
--   Let $N_t\ge3$, fix the object $x$, and for each of finitely many instants $t$ fix the data $y^{data}(t)$, the noise mean $\bar y^{noise}(t)$ and a positive definite noise covariance $R_{y^{noise}(t)}$. Write $J^{data}(x,\alpha(t),t)=\chi^2_{y(t)}(x,\alpha(t))$, so that
--   $$J^{data}(x,\alpha)=\sum_tJ^{data}(x,\alpha(t),t).$$
--   Then a family $\alpha=(\alpha(t))_t$ minimizes $\alpha\mapsto J^{data}(x,\alpha)$ if and only if, for every instant $t$, $\alpha(t)\in\mathbb R^{N_t-1}$ minimizes $a\mapsto J^{data}(x,a,t)$.
--
--   So the minimization over the aberrations splits into independent problems, one per instant, each in $N_t-1$ unknowns.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c009; Sec. 4.B, paragraph 'Minimization w.r.t. alpha', with eq. (35), PDF p. 12

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem alpha_minimization_separates {n : ℕ} (hn : 3 ≤ n) {T P : Type*} [Fintype T] [Fintype P]
    (H : T → Matrix (Baseline n) P ℂ) (ydata ybar : T → Baseline n → ℂ)
    (R : T → Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ)
    (hR : ∀ t, (R t).PosDef) (x : P → ℝ) (α : T → Fin (n - 1) → ℝ) :
    (∀ α' : T → Fin (n - 1) → ℝ,
        myopicCrit H ydata ybar R x α ≤ myopicCrit H ydata ybar R x α') ↔
      ∀ (t : T) (a : Fin (n - 1) → ℝ),
        chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x (α t)) ≤
          chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x a) := by sorry

end Arxiv0812_1178
