-- Prove2me | Theorems.Thm_DRSub4633_lemma_A_3
-- name    : DRSub4633.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:06:26.97356+00:00
-- url     : https://prove2.me/theorems/97558ea4-61a3-463d-8fbd-cc993c6d1469
-- title:
--   Lemma A.3 — prefix inequality
-- statement:
--   For every $T\in[0,1]$ and every real $q$,
--   $$P_q(T)=\int_0^TF_q(t)\,dt\le 0 .$$
--   It is the scalar averaging inequality for intervals that start at time zero.
--
--   Differences from the source: none.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.3, p.44

import Mathlib
import Definitions.Def_DRSub4633_PqPrefix

namespace DRSub4633

/-- **Lemma A.3 (Prefix inequality).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.3, p.44: "For every `T ∈ [0, 1]` and
`q ∈ ℝ`, `P_q(T) ≤ 0`." Here `P_q(T) = ∫_0^T F_q(t) dt` (118). -/
theorem lemma_A_3 (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (q : ℝ) : PqPrefix q T ≤ 0 := by sorry

end DRSub4633
