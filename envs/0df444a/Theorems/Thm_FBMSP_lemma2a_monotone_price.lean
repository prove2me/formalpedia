-- Prove2me | Theorems.Thm_FBMSP_lemma2a_monotone_price
-- name    : FBMSP.lemma2a_monotone_price
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T04:55:29.083477+00:00
-- url     : https://prove2.me/theorems/5ca081ae-25a2-4fbc-ba03-e2264a0e8a90
-- title:
--   Lemma 2(a) — Monotonicity of the least optimal price
-- statement:
--   Under integrable mean-zero MHR error, the least revenue-maximizing price $p_\epsilon(x)$ is nondecreasing for $x\ge0$.
--
--   The statement uses the source's least-optimizer convention. It assumes neither uniqueness nor an interior first-order condition; support-boundary optimal prices remain included.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Lemma 2(a), p.17; proof p.42 (ec8).

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Lemma 2(a): under MHR the least optimal posted price is nondecreasing in
the nonnegative predicted mean.  Draft statement; proof remains open. -/
theorem lemma2a_monotone_price (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) (hmhr : HasMHR η) :
    MonotoneOn (singlePrice η) (Set.Ici (0 : ℝ)) := by sorry

end FBMSP
