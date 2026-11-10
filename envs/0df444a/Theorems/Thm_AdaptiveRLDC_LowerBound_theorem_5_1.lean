-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_theorem_5_1
-- name    : AdaptiveRLDC.LowerBound.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:18.295553+00:00
-- url     : https://prove2.me/theorems/3161bd4c-a62a-4fa1-a624-dc296655feec
-- title:
--   Theorem 5.1 — full-parameter adaptive RLDC blocklength lower bound
-- statement:
--   Fix $\varepsilon>0$ and $\alpha,\beta\in[0,1]$ with $\alpha+\beta>1$, and set $\lambda=\alpha/(\alpha+\beta-1)$. There exists $c=c(\varepsilon,\alpha,\beta)>0$ such that for each fixed $\delta>0$ there is $K_0\ge2$ with the following property. For all $k\ge K_0$, $n,q\ge1$, and every binary code with any valid adaptive $(q,\delta,\alpha,\beta)$-relaxed decoder,
--   $$n\ge c\,q^{-2}\left(\frac{k}{\log_2 k}\right)^{1+1/((\lambda+\varepsilon)q)}.$$
--   No linearity, perfect completeness or constant-query restriction is imposed. At $\alpha=\beta=2/3$, $\lambda=2$ gives the paper's headline bound. This is the mission goal.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random adaptive procedures outputting 0, 1 or abort → PMF laws on published adaptive trees with Option Bool leaves; reason: tree evaluation captures arbitrary real randomness, adaptive choices, early leaves and repeated queries; this generalized item imposes no depth bound
--   - encoding: Ω with subscript ε,α,β and constant decoding radius → a positive c before δ and all sizes and decoders, and a threshold K₀≥2 after the fixed δ; reason: this makes exactly the prescribed parameter dependence explicit and excludes only the undefined logarithmic small-size regime
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Theorem 5.1, printed p.27, PDF p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_AdaptiveDecoder
import Definitions.Def_AdaptiveRLDC_LowerBound_ConstructionParameters

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Theorem 5.1, printed p.27 / PDF p.28, full parameter-dependent blocklength bound.
The positive Ω constant precedes δ and all size, code and decoder variables; the eventual
threshold may depend on the fixed decoding radius. The query bound q may grow with k. -/
theorem theorem_5_1 (ε α β : ℝ) (hε : 0 < ε) (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β ∧ β ≤ 1) (hgap : 1 < α+β) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ K₀ : ℕ, 2 ≤ K₀ ∧
      ∀ (k n q : ℕ), K₀ ≤ k → 1 ≤ n → 1 ≤ q →
      ∀ (C : Cube k → Cube n) (τ : Fin k → PMF (DecodeTree n)),
      IsRelaxedDecoder C q δ α β τ →
        c / (q : ℝ)^2 * ((k : ℝ) / logTwo (k : ℝ)) ^
          (1 + 1 / ((lambda α β + ε) * (q : ℝ))) ≤ (n : ℝ) := by sorry

end AdaptiveRLDC.LowerBound
