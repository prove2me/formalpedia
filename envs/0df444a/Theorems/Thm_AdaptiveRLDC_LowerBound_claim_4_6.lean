-- Prove2me | Theorems.Thm_AdaptiveRLDC_LowerBound_claim_4_6
-- name    : AdaptiveRLDC.LowerBound.claim_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:44.659161+00:00
-- url     : https://prove2.me/theorems/d2091f98-ce07-4f42-a337-f16c11e70b89
-- title:
--   Claim 4.6 — all five elementary CHT properties
-- statement:
--   Let $\rho,\rho'$ be sub-distributions on subsets of $[n]$, $p\in(0,1]$, and $\Gamma>0$. Write $R$ and $\overline R$ for their HT and capped estimators. The following all hold:
--
--   1. $\overline R_\rho(x)\le R_\rho(x)$ for every $x$.
--   2. $\mathbb E_\nu\overline R_\rho\le\mathbb E_\nu R_\rho$ for every input law $\nu$.
--   3. $x\le y$ implies $\overline R_\rho(x)\le\overline R_\rho(y)$.
--   4. $0\le\Delta_i\overline R_\rho(x^{(i)})\le\Gamma$.
--   5. $\rho\le\rho'$ implies $\overline R_\rho(x)\le\overline R_{\rho'}(x)$.
--
--   In particular, the coordinate bound is
--   $$0\le\overline R_\rho(x^{i\to1})-\overline R_\rho(x^{i\to0})\le\Gamma.$$
--   These properties supply the structural interface for later concentration and sampling targets.
--
--   Differences from the source:
--   - encoding: one-based finite coordinate sets [n] → Fin n coordinates and finite subsets; reason: the index shift is a bijection preserving words, cardinalities and probabilities
--   - encoding: random binary vectors and their expectations and event probabilities → exact finite sums under their joint weights, with product weights for independent coordinates; reason: every law on the finite binary cube is represented; independent coordinates may have distinct arbitrary real probabilities
--   - encoding: the attained maximum over real feasible weights in Definition 4.5 → the supremum of the same objective values; reason: the definition proves nonemptiness and an upper bound; finite closed bounded feasibility gives attainment, with no changed instances
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Claim 4.6, printed p.17, PDF p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Definitions.Def_AdaptiveRLDC_LowerBound_CappedEstimator

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

/-- Claim 4.6, printed p.17 / PDF p.18: all five clauses, with arbitrary finite input law. -/
theorem claim_4_6 {n : ℕ} (ρ ρ' : Sets n → ℝ)
    (hρ : IsSubdistribution ρ) (hρ' : IsSubdistribution ρ')
    (p Γ : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hΓ : 0 < Γ) :
    (∀ x, cht ρ p Γ x ≤ ht ρ p x) ∧
    (∀ ν : Cube n → ℝ, FuchsVdGraaf.IsProbDist ν →
      mean ν (cht ρ p Γ) ≤ mean ν (ht ρ p)) ∧
    (∀ x y : Cube n, x ≤ y → cht ρ p Γ x ≤ cht ρ p Γ y) ∧
    (∀ x i, 0 ≤ discreteDerivative (cht ρ p Γ) i x ∧
      discreteDerivative (cht ρ p Γ) i x ≤ Γ) ∧
    ((∀ S, ρ S ≤ ρ' S) → ∀ x, cht ρ p Γ x ≤ cht ρ' p Γ x) := by sorry

end AdaptiveRLDC.LowerBound
