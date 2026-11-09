-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_3_3
-- name    : CommutativeRankNC.Approximation.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:10.409118+00:00
-- url     : https://prove2.me/theorems/459cf3e4-a2fa-4321-949c-2bf38fca590c
-- title:
--   Lemma 3.3 — Positive-probability rank rounding
-- statement:
--   Let $n\ge1$ and $A_i\in\mathbb C^{n\times n}$ span an invertible matrix, as assumed throughout subsection 3.1, with $\operatorname{ds}(A)\le1/(16n)$. Under any four-wise unbiased sign law,
--
--   $$\Pr\!\left[\operatorname{rank}\Bigl(\sum_i\epsilon_iA_i\Bigr)\ge\frac3{25}n\right]>0.$$
--
--   There is consequently a sign vector of strictly positive weight with this rank bound. The same absolute constant $3/25$ applies to every tuple and dimension. Both positive probability and the supported witness are conclusions.
--
--   Differences from the source:
--   - encoding: probabilities and expectations for a finite sign distribution → finite real weighted sums, with seed multiplicities retained in the pushforward law; reason: a finite law needs no analytic integrability assumption and does not replace the seed law by a uniform distinct-image law
--   - encoding: the common absolute constant c₀ → the explicit value c₀=3/25; reason: the proof fixes exactly this value on printed/PDF p.14
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 3.3, PDF/printed p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Scaling

namespace CommutativeRankNC.Approximation

/-- Lemma 3.3, PDF/printed p.12, with the common constant 3/25 from p.14.
Both positive probability and a supported sign witness are retained. -/
theorem lemma_3_3 {n m : ℕ} (hn : 0 < n) (A : Fin m → CMatrix n)
    (hfull : HasFullRankSpan A)
    (hds : doublyStochasticDistance A ≤ 1 / (16*(n : ℝ)))
    (p : SignVector m → ℝ) (hp : TWiseUnbiased 4 p) :
    0 < (∑ e : SignVector m,
      if cZero * (n : ℝ) ≤ ((signedMatrix A e).rank : ℝ) then p e else 0) ∧
    ∃ e : SignVector m, 0 < p e ∧ cZero * (n : ℝ) ≤ ((signedMatrix A e).rank : ℝ) := by sorry

end CommutativeRankNC.Approximation
