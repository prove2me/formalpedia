-- Prove2me | Theorems.Thm_BalkemaDeHaan_ExpDomain_gnedenko_criterion
-- name    : BalkemaDeHaan.ExpDomain.gnedenko_criterion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:43.305981+00:00
-- url     : https://prove2.me/theorems/162be69b-f5b7-4ed5-a4db-8dc61eb5ac84
-- title:
--   Proof of Theorem 3 — Gnedenko's tail criterion for the Gumbel law
-- statement:
--   Let $F=1-R$ be a probability distribution function and let $a_n>0$, $b_n\in\mathbb R$. For these same normalizations, weak convergence of normalized maxima to the Gumbel law is equivalent to convergence of scaled tails:
--
--   $$F(a_nx+b_n)^n\longrightarrow \Lambda(x)=e^{-e^{-x}}\quad\Longleftrightarrow\quad nR(b_n+xa_n)\longrightarrow e^{-x}\qquad(x\in\mathbb R).$$
--
--   The forward implication is the criterion attributed to Gnedenko in the article. The reverse implication is used at the end of Theorem 3's proof to recover the maxima domain from equation (11).
--
--   **Formalization Note** The printed sentence gives the forward implication. The milestone also states the converse because the article invokes it after extending (11) to all real $x$. The limit law is continuous, so weak convergence is pointwise convergence at every real $x$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 798 (PDF 7), proof of Theorems 3 and 4, citing Gnedenko (1943), Theorem 6; p. 799 (PDF 8), (11)

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- Gnedenko's criterion, used in the proof of Theorem 3, p. 798. -/
theorem gnedenko_criterion (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    WeakConvergenceNat (fun n x => (cdf μ (a n * x + b n)) ^ n) lambdaLaw ↔
      TailScaledConvergence μ a b Set.univ := by sorry

end BalkemaDeHaan.ExpDomain
