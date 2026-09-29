-- Prove2me | Theorems.Thm_ABOThreshold_badProb_succ_le
-- name    : ABOThreshold.badProb_succ_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:41:09.313169+00:00
-- url     : https://prove2.me/theorems/1391e40e-76f3-4177-a422-fd3016a68826
-- title:
--   Union bound across one level of concatenation
-- statement:
--   Fix a rectangle size $A$, a tolerance $k$, and an error rate $0\le\eta\le1$. Write $Q(r)=1-P(r)$ for the probability that the faults of an $r$-rectangle fail to be $(r,k)$-sparse.
--
--   For the faults in an $(r+1)$-rectangle not to be $(r+1,k)$-sparse there must be at least $k+1$ of its $A$ constituent $r$-rectangles whose faults are not $(r,k)$-sparse. Since the noise acts independently on distinct sub-rectangles, a union bound over the choices of $k+1$ bad sub-rectangles gives
--
--   $$Q(r+1) \;\le\; \binom{A}{k+1}\,Q(r)^{\,k+1}.$$
--
--   This single-level estimate is the recursion that, iterated, yields the doubly exponential decay of Lemma 10.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, p. 52, proof of Lemma 10 (induction step); Definitions 18-19, pp. 50-51

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem badProb_succ_le (A k : ℕ) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (r : ℕ) :
    badProb A k η (r + 1) ≤ (A.choose (k + 1) : ℝ) * badProb A k η r ^ (k + 1) := by sorry

end ABOThreshold
