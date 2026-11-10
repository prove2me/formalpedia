-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_corollary_5_6
-- name    : AdaptiveRLDC.LowerBound.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:17.709207+00:00
-- url     : https://prove2.me/theorems/ba13bdde-6f1f-4c67-bc8e-2f118d73e299
-- title:
--   Corollary 5.6 — exact-size weighted sub-distribution extraction
-- statement:
--   Let $\mu$ be a sub-distribution of positive total mass supported on sets of size at most $q\ge1$, on a universe of size $n\ge2$. For integer $d>q$, there exist $j\in[d]$, $D\subseteq\operatorname{supp}(\mu)$ and $H$ such that $(\mu|_D)^{\circ H}$ is $(m,n^{1/d})$-spread and
--   $$m=qn^{j/d}/n,\quad |H|=\left\lfloor n/n^{j/d}\right\rfloor=\lfloor q/m\rfloor,\quad\mu(D)\ge(1-q/d)\|\mu\|_1.$$
--   The restricted weights are not renormalized. Exact padding and both floor identities are part of the conclusion.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: punctured weights on subsets of the complement of H → the pushforward on all subsets, zero outside the complement; reason: all preimage weights are added and both support and total mass are preserved
--   - encoding: the positive-domain spread predicate and nonnegative floors → n≥2, q≥1 and natural floors; reason: these expose the domain m>0, r>1 and leave every defined positive-size instance unchanged
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Corollary 5.6, printed p.29, PDF p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_SetOperations
import Definitions.Def_AdaptiveRLDC_LowerBound_ConstructionParameters

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Corollary 5.6, printed p.29 / PDF p.30: restriction, exact padding size and both floors. -/
theorem corollary_5_6 {n q d : ℕ} (hn : 2 ≤ n) (hq : 1 ≤ q) (hd : q < d)
    (μ : Sets n → ℝ) (hμ : IsSubdistribution μ) (hs : SupportedAtMost μ q)
    (hmass : 0 < totalMass μ) :
    ∃ (j : ℕ) (D : Finset (Sets n)) (H : Sets n),
      1 ≤ j ∧ j ≤ d ∧ D ⊆ weightSupport μ ∧
      IsSpread (puncture (restrictWeights μ D) H) (scaleMass n q d j) (spreadRate n d) ∧
      H.card = ⌊(n : ℝ) / (n : ℝ)^((j : ℝ)/(d : ℝ))⌋₊ ∧
      H.card = ⌊(q : ℝ) / scaleMass n q d j⌋₊ ∧
      (1 - (q : ℝ)/(d : ℝ)) * totalMass μ ≤ familyMass μ D := by sorry

end AdaptiveRLDC.LowerBound
