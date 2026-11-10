-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_lemma_3_10
-- name    : AdaptiveRLDC.LowerBound.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:09.567718+00:00
-- url     : https://prove2.me/theorems/23c6c0ac-0d22-4938-9e83-fb08793796df
-- title:
--   Lemma 3.10 — weighted spreadness extraction
-- statement:
--   Let $\mu$ be an arbitrary real-weighted probability distribution supported on subsets of a universe of size $n\ge2$, each of size at most $q\ge1$. Let the integer $d$ satisfy $d>q$. There exist $j\in[d]$, $D\subseteq\operatorname{supp}(\mu)$ and a nonempty $H$ such that $(\mu_D)^{\circ H}$ is $(m,n^{1/d})$-spread and
--   $$m=\frac q{\mu(D)}\frac{n^{j/d}}n,\qquad |H|\le\frac n{n^{j/d}},\qquad\mu(D)\ge1-\frac qd.$$
--   Conditioning precedes puncturing. This preserves both the heavy-set bound and the near-full retained mass for general weighted laws.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: punctured weights on subsets of the complement of H → the pushforward on all subsets, zero outside the complement; reason: all preimage weights are added and both support and total mass are preserved
--   - encoding: the named spread predicate requires positive m and r>1 → q≥1 and n≥2 are explicit; reason: q=0 or n=1 lies outside that predicate domain; the asymptotic coding goal is unaffected
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Lemma 3.10, printed p.15, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_SetOperations
import Definitions.Def_AdaptiveRLDC_LowerBound_ConstructionParameters

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Lemma 3.10, printed p.15 / PDF p.16: weighted extraction, including nonempty H.
Positive-size domain of Definition 3.8 is explicit. -/
theorem lemma_3_10 {n q d : ℕ} (hn : 2 ≤ n) (hq : 1 ≤ q) (hd : q < d)
    (μ : Sets n → ℝ) (hμ : FuchsVdGraaf.IsProbDist μ) (hs : SupportedAtMost μ q) :
    ∃ (j : ℕ) (D : Finset (Sets n)) (H : Sets n),
      1 ≤ j ∧ j ≤ d ∧ D ⊆ weightSupport μ ∧ H.Nonempty ∧
      IsSpread (puncture (conditionWeights μ D) H)
        ((q : ℝ) / familyMass μ D * ((n : ℝ)^((j : ℝ)/(d : ℝ))/(n : ℝ)))
        (spreadRate n d) ∧
      (H.card : ℝ) ≤ (n : ℝ) / (n : ℝ)^((j : ℝ)/(d : ℝ)) ∧
      1 - (q : ℝ)/(d : ℝ) ≤ familyMass μ D := by sorry

end AdaptiveRLDC.LowerBound
