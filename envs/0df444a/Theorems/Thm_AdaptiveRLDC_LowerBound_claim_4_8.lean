-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_claim_4_8
-- name    : AdaptiveRLDC.LowerBound.claim_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:39.825086+00:00
-- url     : https://prove2.me/theorems/5e485dc4-5968-429f-8a53-d2c3addbd10d
-- title:
--   Claim 4.8 — normalized CHT is strongly self-bounding
-- statement:
--   Let $\mu$ be a sub-distribution supported on sets of size at most $q$, with $\Gamma>0$ and $p\in(0,1]$. Then
--   $$f(x)=\overline R_{\mu,p,\Gamma}(x)/\Gamma$$
--   is strongly $(q,0)$-self-bounding in the full existential coordinate-deleted-witness sense. This is the property needed for concentration; the derivative estimates used in the source proof are not assumptions.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Claim 4.8, printed p.18, PDF p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_CappedEstimator
import Definitions.Def_AdaptiveRLDC_LowerBound_SetOperations
import Definitions.Def_AdaptiveRLDC_LowerBound_SelfBounding

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Claim 4.8, printed p.18 / PDF p.19. -/
theorem claim_4_8 {n q : ℕ} (μ : Sets n → ℝ) (hμ : IsSubdistribution μ)
    (hs : SupportedAtMost μ q) (p Γ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hΓ : 0 < Γ) :
    StronglySelfBounding (fun x => cht μ p Γ x / Γ) (q : ℝ) 0 := by sorry

end AdaptiveRLDC.LowerBound
