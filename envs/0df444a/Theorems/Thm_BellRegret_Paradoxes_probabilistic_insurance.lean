-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_probabilistic_insurance
-- name    : BellRegret.Paradoxes.probabilistic_insurance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:09.684973+00:00
-- url     : https://prove2.me/theorems/b6573868-fd91-46a0-a2d9-29d9ddf32b26
-- title:
--   Sec. 2(iii), pp. 974–975 — under (9), (11) holds iff full ≻ probabilistic insurance iff probabilistic ≻ self insurance
-- statement:
--   Let $f:\mathbb R\to\mathbb R$, let $u(x,y)=x+f(x-y)$, let $p\in\mathbb R$ and $0\le q<1$. Consider Table IV: an accident has probability $q$, and the half-price probabilistic insurance pays with probability $\tfrac12$ given an accident; the outcomes are
--   - self insurance: $-1$ on an accident, $0$ otherwise;
--   - full insurance: $-p$ in every state;
--   - probabilistic insurance: $-p$ on an accident when the insurer pays, $-1$ on an accident when it does not, $-p/2$ without accident.
--
--   Suppose full insurance and self insurance are indifferent (equation (9)). Then
--   1. $$f(p/2)-f(-p/2)<\tfrac12\,[f(p)-f(-p)]\qquad(11)$$
--   holds if and only if full insurance is strictly preferred to probabilistic insurance;
--   2. (11) holds if and only if probabilistic insurance is strictly preferred to self insurance.
--
--   So under (11) probabilistic insurance sits strictly between two indifferent options, and when (11) fails both preferences fail (weakly reversed): the decision maker never strictly prefers probabilistic insurance to both of the original options.
--
--   **Formalization Note** The page's intermediate expansions contain misprints: before (10) the right-hand side ends "$(1-q)f(p/2)$", which must be $f(-p/2)$ since $u(-p,-p/2)=-p+f(-p/2)$; on p. 975 the left-hand side has "$(1-q)[-p/2+f(p/2)]$", which must be $f(-p/2)$, and the right-hand side's "$\tfrac12[-1+f(0)]$" lacks the factor $q$. The formalization computes the comparisons from Table IV directly; (9), (10) and (11) as printed are correct. The terms in $f(0)$ cancel, so the page's normalisation $f(0)=0$ is not assumed. "Just reversed" is read as the failure of each strict preference.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, pp. 974–975 (PDF 15–16), Sec. 2(iii), Table IV, displays (9)–(11) and the conclusion "Hence, if (11) is true, …"

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- Sec. 2(iii), pp. 974–975: if full insurance and self insurance are indifferent and
`0 ≤ q < 1`, then (11) `f(p/2) − f(−p/2) < ½[f(p) − f(−p)]` holds if and only if full
insurance is strictly preferred to probabilistic insurance, and if and only if probabilistic
insurance is strictly preferred to self insurance. -/
theorem probabilistic_insurance (f : ℝ → ℝ) (p q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hind : Indiff f (prob3 q) (fullInsurance p) selfInsurance) :
    (f (p / 2) - f (-p / 2) < 1 / 2 * (f p - f (-p)) ↔
      Prefers f (prob3 q) (fullInsurance p) (probInsurance p)) ∧
    (f (p / 2) - f (-p / 2) < 1 / 2 * (f p - f (-p)) ↔
      Prefers f (prob3 q) (probInsurance p) selfInsurance) := by sorry

end BellRegret.Paradoxes
