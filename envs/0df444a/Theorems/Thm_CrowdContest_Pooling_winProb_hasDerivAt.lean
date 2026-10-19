-- Prove2me | Theorems.Thm_CrowdContest_Pooling_winProb_hasDerivAt
-- name    : CrowdContest.Pooling.winProb_hasDerivAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:25.259003+00:00
-- url     : https://prove2.me/theorems/5220d2b7-68b3-415b-b8f4-72ff5353419c
-- title:
--   Proof of Lemma 1, OA p. 1 — the winning probability is differentiable, with derivative h(ξ;n) at equal efforts
-- statement:
--   Let $\varphi$ be a bounded probability density on $\mathbb R$ with cdf $\Psi$, and let $n\ge 2$. The winning probability
--   $$W(x)=\int_{-\infty}^{+\infty}\Psi(x+\xi)^{n-1}\varphi(\xi)\,d\xi$$
--   is differentiable at every $x\in\mathbb R$, with
--   $$W'(x)=\int_{-\infty}^{+\infty}(n-1)\,\Psi(x+\xi)^{n-2}\varphi(x+\xi)\,\varphi(\xi)\,d\xi ,$$
--   and in particular $W'(0)=\int(n-1)\Psi(\xi)^{n-2}\varphi(\xi)^2\,d\xi=h(\xi;n)$.
--
--   This is the first-order condition behind Lemma 1 (and, applied to $\psi^\circ$, Lemma 3): the marginal gain in winning probability from extra effort, at equal efforts, is $h$.
--
--   **Formalization Note** Stated for an arbitrary bounded density so that it applies both to $\psi$ and to $\psi^\circ$; a log-concave density is bounded, and $\psi^\circ\le\sup\psi$. Boundedness replaces any continuity assumption on the density: the derivative of $\Psi$ need not equal $\varphi$ everywhere.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), proof of Lemma 1, OA p. 1 (the FOC); §4.1, p. 15 (h(ξ;n))

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Proof of Lemma 1, OA p. 1 (the first-order condition): for a bounded density `φ` and `n ≥ 2`
the winning probability `x ↦ ∫ Ψ(x + ξ)^{n-1} φ(ξ) dξ` is differentiable, with derivative
`∫ (n - 1) Ψ(x + ξ)^{n-2} φ(x + ξ) φ(ξ) dξ`; at `x = 0` this is `h(ξ; n)`. Stated for any bounded
density so that it applies to `ψ` (Lemma 1) and to `ψ°` (Lemma 3). -/
theorem winProb_hasDerivAt (φ : ℝ → ℝ) (hφ : IsDensity φ) (hbdd : ∃ M, ∀ x, φ x ≤ M)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    HasDerivAt (winProb φ n)
        (∫ ξ, ((n : ℝ) - 1) * cdf φ (x + ξ) ^ (n - 2) * φ (x + ξ) * φ ξ) x ∧
      HasDerivAt (winProb φ n) (hFun φ n) 0 := by sorry

end CrowdContest.Pooling
