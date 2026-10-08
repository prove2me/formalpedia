-- Prove2me | Theorems.Thm_BalkemaDeHaan_ExpDomain_equation_11_all
-- name    : BalkemaDeHaan.ExpDomain.equation_11_all
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:08.872853+00:00
-- url     : https://prove2.me/theorems/23daff19-f3cc-4519-9bca-e82e5f31132b
-- title:
--   (11) on ℝ — continuation from the positive half-line
-- statement:
--   Let $R$ be the survival function of a probability law and let $a_n>0$, $b_n$ be fixed normalizing sequences. If
--
--   $$nR(b_n+xa_n)\longrightarrow e^{-x}\qquad\text{for every }x>0,$$
--
--   then the same limit holds for every real $x$. The conclusion retains the original normalization sequences. This continuation principle closes the reverse direction of Theorem 3.
--
--   **Formalization Note** The statement is about the tail $R$ of a probability measure, so $R$ is antitone and takes values in $[0,1]$. The proof passage uses the convergence-of-types remark and the constant $\log 2$; it is not inserted as a hypothesis.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 799 (PDF 8), proof of Theorem 3, continuation of (11)

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open MeasureTheory

/-- Continuation of equation (11) from `x > 0` to all real `x`, p. 799. -/
theorem equation_11_all (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h : TailScaledConvergence μ a b (Set.Ioi 0)) :
    TailScaledConvergence μ a b Set.univ := by sorry

end BalkemaDeHaan.ExpDomain
