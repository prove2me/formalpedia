-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_claim_5_9
-- name    : AdaptiveRLDC.LowerBound.claim_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:59:39.480361+00:00
-- url     : https://prove2.me/theorems/791e133d-0a99-4977-b681-f7abe68a7adf
-- title:
--   Claim 5.9 — simultaneous soundness for every guess
-- statement:
--   Fix $\varepsilon>0$, $\alpha,\beta\in[0,1]$ with $\alpha+\beta>1$. For all sufficiently large constants $D=D(\varepsilon,\alpha,\beta)$, and each fixed radius $\delta>0$, there is a blocklength threshold independent of $k,q,C$ and the decoder. For every larger blocklength and valid $q\ge1$ relaxed decoder, use the exact parameters $d,r,p,m_j,\theta$ of Construction 5.7 and assume $p<1$. For each fixed message $x$ and index $i$, with $b^*=x_i$,
--   $$\Pr_W\left[\forall j\in[d],\ \forall H:|H|=\lfloor q/m_j\rfloor,\ \forall\kappa:H\to\{0,1\},\ \overline R_{m_j,H,\kappa,1-b^*}(1_W)<\theta\right]\ge5/6.$$
--   One sampling event controls every guess at once. The source large-size regime and choice of sufficiently large $D$ are made explicit.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random adaptive procedures outputting 0, 1 or abort → PMF laws on published adaptive trees with Option Bool leaves; reason: tree evaluation captures arbitrary real randomness, adaptive choices, early leaves and repeated queries; this generalized item imposes no depth bound
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
--   - encoding: punctured weights on subsets of the complement of H → the pushforward on all subsets, zero outside the complement; reason: all preimage weights are added and both support and total mass are preserved
--   - encoding: sufficiently large D,n under the standing fixed parameters and p<1 → ∃D₀>0, ∀D≥D₀, ∀δ>0, ∃N≥2, ∀k,n,q with n≥N and q≥1; reason: the constant threshold precedes size and decoder data; N may depend on δ, while D₀ does not
--   - encoding: probability over W sampled independently with rate p → eventMass of sampleWeight p on the finite power set; reason: the product weight is exactly the source binomial subset law, with arbitrary real p and no rationality restriction
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Claim 5.9, printed p.31, PDF p.32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_Construction

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Claim 5.9, printed p.31 / PDF p.32, with the sufficiently-large D,n regime explicit.
One sample event quantifies over every scale, H and assignment simultaneously. -/
theorem claim_5_9 (ε α β : ℝ) (hε : 0 < ε) (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hgap : 1 < α+β) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 2 ≤ N ∧
      ∀ (k n q : ℕ), N ≤ n → 1 ≤ q →
      ∀ (C : Cube k → Cube n) (τ : Fin k → PMF (DecodeTree n)),
      IsRelaxedDecoder C q δ α β τ →
      samplingRate D ε α β n q < 1 → ∀ (x : Cube k) (i : Fin k),
      5/6 ≤ eventMass (sampleWeight (samplingRate D ε α β n q)) (fun W =>
        ∀ (j : Fin (constructionD ε α β q)) (H : Sets n),
          H.card = ⌊(q : ℝ) / scaleMass n q (constructionD ε α β q) (j.val+1)⌋₊ →
          ∀ κ : H → Bool,
          guessedEstimate (τ i) (C x) (scaleMass n q (constructionD ε α β q) (j.val+1))
            (samplingRate D ε α β n q) (spreadRate n (constructionD ε α β q)) H κ (!(x i)) W <
              threshold α β q (constructionD ε α β q)) := by sorry

end AdaptiveRLDC.LowerBound
