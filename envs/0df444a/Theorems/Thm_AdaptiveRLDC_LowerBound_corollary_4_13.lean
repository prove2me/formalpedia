-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_corollary_4_13
-- name    : AdaptiveRLDC.LowerBound.corollary_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:35.25476+00:00
-- url     : https://prove2.me/theorems/3cb4392f-d710-4b7b-bba7-672485a52007
-- title:
--   Corollary 4.13 — both CHT concentration tails
-- statement:
--   Let $X$ have independent Bernoulli$(p)$ coordinates, $p\in(0,1]$, and let $\mu$ be a sub-distribution supported on sets of size at most $q\ge1$. For $\Gamma>0$, $\theta\in(0,1)$ and $\gamma>0$, put $Z=\overline R_{\mu,p,\Gamma}(X)$. Both implications hold:
--   $$\mathbb EZ\le\theta-\gamma\ \Longrightarrow\ \Pr[Z\ge\theta]\le e^{-\gamma^2/(2q\Gamma)},$$
--   $$\mathbb EZ\ge\theta+\gamma\ \Longrightarrow\ \Pr[Z\le\theta]\le e^{-\gamma^2/(2q\Gamma)}.$$
--   The exact common denominator and both non-strict events are retained. This gives the source estimator's two-tail interface.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random binary vectors and their expectations and event probabilities → exact finite sums under their joint weights, with product weights for independent coordinates; reason: every law on the finite binary cube is represented; independent coordinates may have distinct arbitrary real probabilities
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
--   - encoding: the positive query-size regime used explicitly in the proof on printed p.22 → q≥1 is a binder hypothesis; reason: the denominator 2qΓ and application of Theorem 4.12 require the source positive-size convention
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Corollary 4.13, printed p.21, PDF p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_CappedEstimator
import Definitions.Def_AdaptiveRLDC_LowerBound_SetOperations

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Corollary 4.13, printed p.21 / PDF p.22: both tails with the exact denominator. -/
theorem corollary_4_13 {n q : ℕ} (hq : 1 ≤ q) (μ : Sets n → ℝ)
    (hμ : IsSubdistribution μ) (hs : SupportedAtMost μ q)
    (p Γ θ γ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hΓ : 0 < Γ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) :
    (mean (productWeight (fun _ : Fin n => p)) (cht μ p Γ) ≤ θ-γ →
      eventMass (productWeight (fun _ : Fin n => p)) (fun x => θ ≤ cht μ p Γ x) ≤
        Real.exp (-(γ^2)/(2*(q : ℝ)*Γ))) ∧
    (θ+γ ≤ mean (productWeight (fun _ : Fin n => p)) (cht μ p Γ) →
      eventMass (productWeight (fun _ : Fin n => p)) (fun x => cht μ p Γ x ≤ θ) ≤
        Real.exp (-(γ^2)/(2*(q : ℝ)*Γ))) := by sorry

end AdaptiveRLDC.LowerBound
