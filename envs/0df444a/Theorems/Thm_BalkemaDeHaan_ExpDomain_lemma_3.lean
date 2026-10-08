-- Prove2me | Theorems.Thm_BalkemaDeHaan_ExpDomain_lemma_3
-- name    : BalkemaDeHaan.ExpDomain.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:26.289241+00:00
-- url     : https://prove2.me/theorems/955349b5-2967-4914-98d4-90ce73521348
-- title:
--   Lemma 3 — the tail jumps become negligible
-- statement:
--   Let $F=1-R$ belong to the residual-life domain of attraction of a continuous distribution function $G$. Then the left and right values of its survival function satisfy
--
--   $$\frac{R(x-0)}{R(x+0)}\longrightarrow 1\qquad (x\to\infty).$$
--
--   Thus individual atoms become negligible compared with the survival probability at great ages. This permits the continuous-time normalization to be sampled at levels with tail probability approximately $1/n$.
--
--   **Formalization Note** $R(x-0)=\Pr(X\ge x)$ and $R(x+0)=\Pr(X>x)$. The domain hypothesis includes $R(x)>0$ for every $x$, so the quotient has a positive denominator.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 798 (PDF 7), Lemma 3

import Definitions.Def_BalkemaDeHaan_ExpDomain_Domains

namespace BalkemaDeHaan.ExpDomain

open Filter MeasureTheory ProbabilityTheory

/-- Lemma 3, p. 798: asymptotically negligible jumps of the BalkemaDeHaan.LimitTypes.tail. -/
theorem lemma_3 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hG : Continuous (cdf ν)) (h : InDr μ (cdf ν)) :
    Tendsto (fun x : ℝ => (μ (Set.Ici x)).toReal / BalkemaDeHaan.LimitTypes.tail μ x) atTop (nhds 1) := by sorry

end BalkemaDeHaan.ExpDomain
