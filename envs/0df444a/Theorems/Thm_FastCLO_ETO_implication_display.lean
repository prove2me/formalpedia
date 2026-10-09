-- Prove2me | Theorems.Thm_FastCLO_ETO_implication_display
-- name    : FastCLO.ETO.implication_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:51.218392+00:00
-- url     : https://prove2.me/theorems/0cc6aa70-73e2-4ff3-be2b-15da70ffb3f0
-- title:
--   Proof of Theorem 8, implication display — a suboptimal plug-in decision with estimation error ≤ ε forces 0 < Δ(x) ≤ 2Bε
-- statement:
--   Let $\mathcal Z$ be a polytope with norm bound $B$ and extreme points $\mathcal Z^\angle$, let $f^*$ be the regression function of an instance, and let $\pi$ be a plug-$f$-in policy for some $f : \mathbb R^p \to \mathbb R^d$, so $\pi(x) \in \mathcal Z^\angle$ minimizes $f(x)^\top z$ over $\mathcal Z$. Fix $x$ and $\varepsilon \in \mathbb R$. If
--
--   1. the decision $\pi(x)$ is strictly suboptimal for the true cost: $f^*(x)^\top \pi(x) > \min_{z \in \mathcal Z} f^*(x)^\top z$, and
--   2. the estimation error is small: $\|f^*(x) - f(x)\| \le \varepsilon$,
--
--   then the gap $\Delta(x)$ satisfies
--
--   $$0 < \Delta(x) \le 2B\varepsilon.$$
--
--   This is the step of the proof of Theorem 8 that converts a decision error into a statement about the gap: because plug-in decisions are extreme points, a wrong decision can only occur at points where the gap is positive and at most a multiple of the estimation error. The noise condition then controls how likely such points are. In the paper $\varepsilon = 2^r\delta$.
--
--   **Formalization Note** Suboptimality is measured against the optimal value, which equals $f^*(x)^\top\pi_{f^*}(x)$. That $\mathcal Z^\angle$ is finite, which the positivity of $\Delta(x)$ relies on, is a fact about polytopes to be proved, not a hypothesis.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 8 (Appendix A.5), the implication display, p. 30

import Mathlib
import Definitions.Def_FastCLO_ETO_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace FastCLO.ETO

/-- **Proof of Theorem 8, the implication display** (Hu, Kallus, Mao, *Fast Rates for Contextual
Linear Optimization*, arXiv:2011.03030v3, Appendix A.5, p. 30): "`f*(X)ᵀ(π_f̂(X) − π_f*(X)) > 0,
‖f*(X) − f̂(X)‖ ≤ 2^r δ ⟹ 0 < f*(X)ᵀ(π_f̂(X) − π_f*(X)) ≤ 2^{r+1}Bδ ⟹ 0 < Δ(X) ≤ 2^{r+1}Bδ, since
π_f(x) ∈ Z∠ is always an extreme point, for any f and x."

For a plug-in policy `π` for an estimate `f` and a point `x`: if the decision `π(x)` is strictly
suboptimal for the true cost `f*(x)` and `‖f*(x) − f(x)‖ ≤ ε`, then `0 < Δ(x) ≤ 2Bε`.

Formalization Note: `ε` stands for the page's `2^r δ`. Suboptimality is measured against the
optimal value `optVal` (equal to `f*(x)ᵀπ_f*(x)`, since `π_f*(x) ∈ Z*(x)`). The gap `Δ` uses real
`sInf` over `Z∠ \ Z*(x)`, a nonempty finite set whenever `Z*(x) ≠ Z`; finiteness of `Z∠` is a
fact to prove, not a hypothesis. -/
theorem implication_display {p d : ℕ} (P : Polytope d) (I : Instance p d) (f π : FastCLO.ERM.Vec p → FastCLO.ERM.Vec d)
    (hπ : IsPlugIn P f π) (x : FastCLO.ERM.Vec p) (ε : ℝ)
    (hsub : 0 < ⟪I.fstar x, π x⟫_ℝ - optVal P I x) (herr : ‖I.fstar x - f x‖ ≤ ε) :
    0 < gap P I x ∧ gap P I x ≤ 2 * P.B * ε := by sorry

end FastCLO.ETO
