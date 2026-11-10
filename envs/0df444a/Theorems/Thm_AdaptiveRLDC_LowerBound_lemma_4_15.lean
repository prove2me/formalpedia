-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_lemma_4_15
-- name    : AdaptiveRLDC.LowerBound.lemma_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:48.36021+00:00
-- url     : https://prove2.me/theorems/8d2ae508-b88a-49f3-9752-3ff4accf83bb
-- title:
--   Lemma 4.15 — explicit spreadness bound on capping bias
-- statement:
--   Let $\mu$ be an $(m,r)$-spread sub-distribution supported on sets of size at most $q$. Let $p\in(0,1]$, $pr\ge2(q-1)$ and $\Gamma=2m/(pr)$. For independent Bernoulli$(p)$ coordinates $X$,
--   $$0\le\mathbb ER_{\mu,p}(X)-\mathbb E\overline R_{\mu,p,\Gamma}(X)\le\frac{q(q-1)}{2pr}.$$
--   This is the explicit inequality proved on printed p.24 (PDF p.25), giving the stated $O(q^2/(pr))$ conclusion with a universal constant. No derivative, trimming or variance result is assumed.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random binary vectors and their expectations and event probabilities → exact finite sums under their joint weights, with product weights for independent coordinates; reason: every law on the finite binary cube is represented; independent coordinates may have distinct arbitrary real probabilities
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
--   - generalization: the displayed O(q²/(pr)) conclusion of Lemma 4.15 → the explicit nonnegative q(q−1)/(2pr) bound from its proof on printed p.24; reason: the quantitative source proof implies the printed asymptotic bound uniformly, including q=0 and q=1
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Lemma 4.15, printed p.23, PDF p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_SetOperations
import Definitions.Def_AdaptiveRLDC_LowerBound_CappedEstimator

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Lemma 4.15, printed p.23 / PDF p.24; the explicit constant is proved on
printed p.24 / PDF p.25. No internal trimming/variance claims are hypotheses. -/
theorem lemma_4_15 {n q : ℕ} (μ : Sets n → ℝ) (hs : SupportedAtMost μ q)
    (m r : ℝ) (hspread : IsSpread μ m r) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpr : 2*((q : ℝ)-1) ≤ p*r) :
    0 ≤ mean (productWeight (fun _ : Fin n => p)) (ht μ p) -
      mean (productWeight (fun _ : Fin n => p)) (cht μ p (2*m/(p*r))) ∧
    mean (productWeight (fun _ : Fin n => p)) (ht μ p) -
      mean (productWeight (fun _ : Fin n => p)) (cht μ p (2*m/(p*r))) ≤
        (q : ℝ)*((q : ℝ)-1)/(2*p*r) := by sorry

end AdaptiveRLDC.LowerBound
