-- Prove2me | Theorems.Thm_DRSub4633_lemma_A_4
-- name    : DRSub4633.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:10:05.166208+00:00
-- url     : https://prove2.me/theorems/17984850-e328-4213-9066-a6db581e486c
-- title:
--   Lemma A.4 — intervals $[\tau,1]$ with $\tau\le t_0$
-- statement:
--   For $0\le\tau\le t_0$ and $1/2\le q\le 1$,
--   $$P_q(1)-P_q(\tau)\le B(\tau).$$
--
--   Differences from the source: none.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.4, p.46

import Mathlib
import Definitions.Def_DRSub4633_PqPrefix
import Definitions.Def_DRSub4633_Bbudget
import Definitions.Def_DRSub4633_t0

namespace DRSub4633

/-- **Lemma A.4 (Intervals `[τ, 1]` with `τ ≤ t₀`).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.4, p.46: "For
`0 ≤ τ ≤ t₀` and `1/2 ≤ q ≤ 1`, `P_q(1) − P_q(τ) ≤ B(τ)`." -/
theorem lemma_A_4 (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ t0) (q : ℝ) (hq0 : 1 / 2 ≤ q) (hq1 : q ≤ 1) :
    PqPrefix q 1 - PqPrefix q τ ≤ Bbudget τ := by sorry

end DRSub4633
