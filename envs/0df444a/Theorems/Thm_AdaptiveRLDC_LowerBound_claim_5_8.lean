-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_claim_5_8
-- name    : AdaptiveRLDC.LowerBound.claim_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:59:33.698567+00:00
-- url     : https://prove2.me/theorems/a2af35fc-dbfa-434c-920b-4b6e63366b08
-- title:
--   Claim 5.8 — the estimator depends only on the sampled view
-- statement:
--   Fix a tree law $\tau$, positive parameters $m,p$ with $p\le1$, $r>1$, and a guess $H,\kappa,b$. If words $c,c'$ agree on $W$, then
--   $$\overline R^{c}_{m,H,\kappa,b}(1_W)=\overline R^{c'}_{m,H,\kappa,b}(1_W).$$
--   The weights are computed from tree execution on the guessed corruption of each word. This is an invariance statement for actual estimators and guarantees that the tests use only observable sampled bits.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random adaptive procedures outputting 0, 1 or abort → PMF laws on published adaptive trees with Option Bool leaves; reason: tree evaluation captures arbitrary real randomness, adaptive choices, early leaves and repeated queries; this generalized item imposes no depth bound
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
--   - encoding: punctured weights on subsets of the complement of H → the pushforward on all subsets, zero outside the complement; reason: all preimage weights are added and both support and total mass are preserved
--   - generalization: the tree laws, scales and caps from Construction 5.7 → arbitrary tree laws and all m>0, p∈(0,1], r>1; reason: the source construction is a specialization and the source invariance argument needs no decoder-correctness or size condition
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Claim 5.8, printed p.31, PDF p.32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_Construction

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Claim 5.8, printed p.31 / PDF p.32; the invariance holds for arbitrary tree laws and
positive estimator parameters, extending the particular construction's parameters. -/
theorem claim_5_8 {n : ℕ} (τ : PMF (DecodeTree n)) (c c' : Cube n)
    (m p r : ℝ) (hm : 0 < m) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 1 < r)
    (H : Sets n) (κ : H → Bool) (b : Bool) (W : Sets n)
    (hview : ∀ i ∈ W, c i = c' i) :
    guessedEstimate τ c m p r H κ b W = guessedEstimate τ c' m p r H κ b W := by sorry

end AdaptiveRLDC.LowerBound
