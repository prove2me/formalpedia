-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_claim_5_10
-- name    : AdaptiveRLDC.LowerBound.claim_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:59:35.778842+00:00
-- url     : https://prove2.me/theorems/6a8c28ba-c4d0-4c8a-997f-4ede723e729d
-- title:
--   Claim 5.10 — one fixed correct guess succeeds
-- statement:
--   Under Construction 5.7 with $\varepsilon>0$, $\alpha,\beta\in[0,1]$, $\alpha+\beta>1$, sufficiently large $D=D(\varepsilon,\alpha,\beta)$, each fixed $\delta>0$ and sufficiently large $n$, let $C$ have a valid $q\ge1$ relaxed decoder and let $p<1$. For each fixed message $x$ and index $i$, there exist $j\in[d]$, $H$ with $|H|=\lfloor q/m_j\rfloor$ and an assignment $\kappa$ such that
--   $$\Pr_W[\overline R_{m_j,H,\kappa,x_i}(1_W)\ge\theta]\ge5/6.$$
--   The guess is chosen before sampling. The statement does not require simultaneous recovery for all indices or success of every guess.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random adaptive procedures outputting 0, 1 or abort → PMF laws on published adaptive trees with Option Bool leaves; reason: tree evaluation captures arbitrary real randomness, adaptive choices, early leaves and repeated queries; this generalized item imposes no depth bound
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
--   - encoding: punctured weights on subsets of the complement of H → the pushforward on all subsets, zero outside the complement; reason: all preimage weights are added and both support and total mass are preserved
--   - encoding: sufficiently large construction constants and blocklengths → uniform D₀ before D,δ and a threshold N before all size and decoder data; reason: this exposes the fixed-parameter asymptotic convention and retains the p<1 standing assumption
--   - encoding: probability over W sampled independently with rate p → eventMass of sampleWeight p on the finite power set; reason: the product weight is exactly the source binomial subset law, with arbitrary real p and no rationality restriction
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Claim 5.10, printed p.31, PDF p.32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_Construction

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Claim 5.10, printed p.31 / PDF p.32: the guess is fixed before W is sampled. -/
theorem claim_5_10 (ε α β : ℝ) (hε : 0 < ε) (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hgap : 1 < α+β) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 2 ≤ N ∧
      ∀ (k n q : ℕ), N ≤ n → 1 ≤ q →
      ∀ (C : Cube k → Cube n) (τ : Fin k → PMF (DecodeTree n)),
      IsRelaxedDecoder C q δ α β τ →
      samplingRate D ε α β n q < 1 → ∀ (x : Cube k) (i : Fin k),
      ∃ (j : Fin (constructionD ε α β q)) (H : Sets n) (κ : H → Bool),
        H.card = ⌊(q : ℝ) / scaleMass n q (constructionD ε α β q) (j.val+1)⌋₊ ∧
        5/6 ≤ eventMass (sampleWeight (samplingRate D ε α β n q)) (fun W =>
          threshold α β q (constructionD ε α β q) ≤
          guessedEstimate (τ i) (C x) (scaleMass n q (constructionD ε α β q) (j.val+1))
            (samplingRate D ε α β n q) (spreadRate n (constructionD ε α β q)) H κ (x i) W) := by sorry

end AdaptiveRLDC.LowerBound
