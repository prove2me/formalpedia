-- Prove2me | Theorems.Thm_CrowdContest_Pooling_lemma_4
-- name    : CrowdContest.Pooling.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:18.703967+00:00
-- url     : https://prove2.me/theorems/7bf53ac5-a4f6-4d77-a3bb-7b2d37b88c47
-- title:
--   Lemma 4, p. 17 — E(ξ¹_(n)) + E(ξ²_(n)) > E((ξ¹ + ξ²)_(n)), n ≥ 2, under Assumption (R)
-- statement:
--   Let $n\ge 2$ and let $\xi^1,\xi^2$ be independent random factors with a common symmetric log-concave density $\psi$; let $\psi^\circ$ be the density of $\xi^1+\xi^2$. Assume the regularity condition (R): there is $u_0$ with $2\Psi^{-1}(u)-\Psi^{\circ-1}(u)<0$ on $(0,u_0)$ and $>0$ on $(u_0,1)$. Then the expected maxima of $n$ independent copies satisfy
--   $$\mathsf E(\xi^1_{(n)})+\mathsf E(\xi^2_{(n)})>\mathsf E\big((\xi^1+\xi^2)_{(n)}\big).$$
--
--   The sum of the best realizations along the two attributes is, in expectation, strictly larger than the best realization of the sum. This is the combination effect, part (i) of Proposition 1.
--
--   **Formalization Note** Each expected maximum is $\int\xi\,n\Psi(\xi)^{n-1}\psi(\xi)\,d\xi$ for the relevant density. Assumption (R) is a hypothesis, as the paper requires it right before the lemma (p. 16); the paper's remark that all symmetric log-concave distributions satisfy it is cited from the literature and is not part of this statement.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), Lemma 4, p. 17; proof OA p. 2

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density
import Definitions.Def_CrowdContest_Pooling_Setting

open MeasureTheory

namespace CrowdContest.Pooling

/-- Lemma 4, p. 17: for a symmetric log-concave density `ψ` satisfying Assumption (R) and
`n ≥ 2`, `E(ξ¹_(n)) + E(ξ²_(n)) > E((ξ¹ + ξ²)_(n))`, where `ξ¹, ξ²` have density `ψ` and
`ξ¹ + ξ²` has density `ψ° = convDensity ψ`. -/
theorem lemma_4 (n : ℕ) (hn : 2 ≤ n) (ψ : ℝ → ℝ) (hψ : IsSymLogConcaveDensity ψ)
    (hR : AssumptionR ψ) :
    expMax (convDensity ψ) n < expMax ψ n + expMax ψ n := by sorry

end CrowdContest.Pooling
