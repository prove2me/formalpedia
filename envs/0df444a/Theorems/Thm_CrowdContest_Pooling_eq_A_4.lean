-- Prove2me | Theorems.Thm_CrowdContest_Pooling_eq_A_4
-- name    : CrowdContest.Pooling.eq_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:40.834516+00:00
-- url     : https://prove2.me/theorems/5154299a-caf2-450b-ad4e-9a9338600fc1
-- title:
--   (A.4), proof of Lemma 4, OA p. 2 — E(ξ_(n)) = ∫₀¹ Ψ⁻¹(u) n uⁿ⁻¹ du
-- statement:
--   Let $\varphi$ be a probability density on $\mathbb R$ with a finite first moment, $\int|x|\varphi(x)\,dx<\infty$, let $\Psi$ be its cdf and $\Psi^{-1}(u)=\inf\{x:u\le\Psi(x)\}$ its quantile function, and let $n\ge 1$. Then the expected maximum of $n$ independent draws from $\varphi$ has the quantile representation
--   $$\int_{-\infty}^{+\infty}\xi\,n\,\Psi(\xi)^{n-1}\varphi(\xi)\,d\xi=\int_0^1\Psi^{-1}(u)\,n\,u^{n-1}\,du .$$
--
--   This is display (A.4) of the proof of Lemma 4. Applied to $\psi$ and to $\psi^\circ$ it writes $\Delta^\xi_n$ as a single integral over $(0,1)$, which is how Assumption (R) enters; with $n=1$ it gives $\int_0^1\Psi^{-1}(u)\,du=\mathsf E(\xi)$.
--
--   **Formalization Note** The page proves the identity for $\xi^l$ and says "similarly" for $\xi^\circ$; it is stated here for any density with a finite mean, which covers both. The finite-mean hypothesis is needed because the left side is a Bochner integral, which is $0$ when the integrand is not integrable. The quantile's values at $u=0,1$ are junk and do not affect the interval integral.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), proof of Lemma 4, display (A.4), OA p. 2

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density

open MeasureTheory

namespace CrowdContest.Pooling

/-- (A.4), proof of Lemma 4, OA p. 2: for a density `φ` with a finite first moment and `n ≥ 1`,
the expected maximum of `n` independent draws equals its quantile form,
`∫ ξ n Ψ(ξ)^{n-1} φ(ξ) dξ = ∫₀¹ Ψ⁻¹(u) n u^{n-1} du`. Stated for a general density so that it
covers both `ψ` and `ψ° = convDensity ψ` ("Similarly, E(ξ°_(n)) = …"). -/
theorem eq_A_4 (φ : ℝ → ℝ) (hφ : IsDensity φ) (hmean : Integrable (fun x => x * φ x))
    (n : ℕ) (hn : 1 ≤ n) :
    expMax φ n = ∫ u in (0 : ℝ)..1, quantile (cdf φ) u * (n : ℝ) * u ^ (n - 1) := by sorry

end CrowdContest.Pooling
