-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_rate_bound
-- name    : BesbesZeevi.SingleParam.rate_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:01:19.044217+00:00
-- url     : https://prove2.me/theorems/24ba44e9-f987-4413-a50e-2f7aa8bbc9aa
-- title:
--   Rate arithmetic: $n^{a_{\ell_n}-1}\le e\,n^{-1/2}$
-- statement:
--   Let $a_\ell=2^{\ell-1}/(2^\ell-1)$ and $\ell_n=\lceil(\log2)^{-1}\log\log n\rceil$. Then for every integer $n\ge8$ (so that $\log n\ge2$),
--
--   $$
--   n^{a_{\ell_n}-1}\le e\,n^{-1/2}.
--   $$
--
--   This deterministic estimate turns (A-31) into the rate $(\log\log n)(\log n)^{1/2}/n^{1/2}$ of Proposition 5.
--
--   **Formalization Note** The paper states the estimate for its real-valued $\ell_n$; with $\ell_n$ rounded up it holds as soon as $\log n\ge2$, because $2^{\ell_n}\ge\log n$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 37 (PDF p. 39), proof of Proposition 5 (sentence after (A-31))

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_Tuning

namespace BesbesZeevi.SingleParam

/-- Rate arithmetic (Besbes–Zeevi 2009, proof of Proposition 5, p. 37): with
`a_ℓ = 2^{ℓ-1}/(2^ℓ - 1)` and `ℓ_n = ⌈log₂ log n⌉`, `n^{a_{ℓ_n} - 1} ≤ e · n^{-1/2}` for every
`n ≥ 8` (i.e. `log n ≥ 2`). -/
theorem rate_bound (n : ℕ) (hn : 8 ≤ n) :
    (n : ℝ) ^ (aCoef (numStages n) - 1) ≤ Real.exp 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end BesbesZeevi.SingleParam
