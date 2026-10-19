-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_1
-- name    : CorrelatedTrials.Consistency.lemma_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:20.573426+00:00
-- url     : https://prove2.me/theorems/3a7bca01-802f-462a-9b07-2df03fb05d3b
-- title:
--   Lemma EC.1 (first inequality), p. ec3 — $\nu^{cKG_1}_i\le\nu^*_i$
-- statement:
--   Let $(\mu,\Sigma)$ be a belief with $\Sigma$ positive definite, let $\lambda_j>0$ and $c_j>0$ for every arm $j$, and let $i$ be an arm. Then the one-step index (EC.6) with $\tau=1$ is at most the cPDE allocation index (EC.8):
--
--   $$
--   \nu^{cKG_1}_i(\mu,\Sigma)\le\nu^*_i(\mu,\Sigma).
--   $$
--
--   Together with $\nu^{cKG_1}_i\ge-1$ it gives $\nu^*_i\ge-1$, which the proof of Theorem 1 uses to transfer the consistency of one-step policies to cPDE.
--
--   **Formalization Note** Only the first inequality of the printed Lemma EC.1 is stated. The printed second inequality $\nu^*_i\le\nu^{cKG_1:\bar\tau}_i$, with $\bar\tau$ of (EC.11), is false as printed: $\bar\tau$ is not invariant under a change of currency, and for $M=2$, $\mu=(0,10^{-3})$, $\Sigma=\mathrm{diag}(10^{-6},10^{-6})$, $\lambda=(10^{-4},10^{-4})$, $c=(10^{-7},10^{-7})$ one gets $\bar\tau=1$ and $\nu^{cKG_1:1}_1\approx-1$, while the deterministic lookahead $T\equiv242$ already gives a value above $240$. That inequality is not posed.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec3, Lemma EC.1 (first inequality)

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_AllocationIndex

namespace CorrelatedTrials.Consistency

/-- Lemma EC.1, first inequality (Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec3, Lemma EC.1):
"ν^{cKG1}_i(µ^t, Σ^t) ≤ ν*_i(µ^t, Σ^t)".

For every belief `(µ, Σ)` with `Σ` positive definite, positive sampling variances and positive
costs, the one-step cKG index (EC.6) with `τ = 1` is at most the cPDE allocation index (EC.8).

Formalization Note: only the first inequality of Lemma EC.1 is stated. The printed second
inequality `ν*_i ≤ ν^{cKG1:τ̄}_i`, with `τ̄` of (EC.11), is false as printed (`τ̄` is not invariant
under a change of currency; e.g. `M = 2`, `µ = (0, 10⁻³)`, `Σ = diag(10⁻⁶, 10⁻⁶)`,
`λ = (10⁻⁴, 10⁻⁴)`, `c = (10⁻⁷, 10⁻⁷)` gives `τ̄ = 1` and `ν^{cKG1:1}_1 ≈ −1`, while the
lookahead `T ≡ 242` already gives a value above `240`). It is not posed. -/
theorem lemma_EC_1 {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (hSig : Sig.PosDef) (hlam : ∀ j, 0 < lam j) (hc : ∀ j, 0 < c j) :
    nuCKG1 lam c mu Sig i ≤ nuStar lam c mu Sig i := by sorry

end CorrelatedTrials.Consistency
