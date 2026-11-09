-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_claim_3_4
-- name    : CommutativeRankNC.Approximation.claim_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:21.571129+00:00
-- url     : https://prove2.me/theorems/95543db7-ceca-4ced-b552-52395a70d7b7
-- title:
--   Claim 3.4 — Fourth moment bound
-- statement:
--   Let $n\ge1$ and $A_i\in\mathbb C^{n\times n}$ satisfy the subsection's full-rank-span assumption and $\operatorname{ds}(A)\le1/(16n)$. Let $p$ be any four-wise unbiased sign law, put $S=\sum_i\epsilon_iA_i$, $M=\sum_iA_iA_i^*$ and $N=\sum_iA_i^*A_i$. Then
--
--   $$\mathbb E\operatorname{Tr}((S^*S)^2)\le\operatorname{Tr}(N^2)+2\operatorname{Tr}(M^2).$$
--
--   The traces are taken as real values; the expectation is a finite weighted sum. This bounds the fourth singular-value moment used in rank rounding. All enclosing standing hypotheses are carried explicitly.
--
--   Differences from the source:
--   - encoding: probabilities and expectations for a finite sign distribution → finite real weighted sums, with seed multiplicities retained in the pushforward law; reason: a finite law needs no analytic integrability assumption and does not replace the seed law by a uniform distinct-image law
--   - encoding: real traces of positive Hermitian expressions → real parts of the corresponding complex matrix traces; reason: these expressions have real trace; no order on complex numbers is postulated
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Claim 3.4, PDF/printed p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Scaling

namespace CommutativeRankNC.Approximation

/-- Claim 3.4, PDF/printed p.12 (proof p.13), carrying the enclosing
subsection and Lemma 3.3 hypotheses. Traces are their real values. -/
theorem claim_3_4 {n m : ℕ} (hn : 0 < n) (A : Fin m → CMatrix n)
    (hfull : HasFullRankSpan A)
    (hds : doublyStochasticDistance A ≤ 1 / (16*(n : ℝ)))
    (p : SignVector m → ℝ) (hp : TWiseUnbiased 4 p) :
    ∑ e, p e * fourthMoment A e ≤
      (Matrix.trace (rightMoment A ^ 2)).re + 2 * (Matrix.trace (leftMoment A ^ 2)).re := by sorry

end CommutativeRankNC.Approximation
