-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_2
-- name    : AdvMultiplayer.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:26.504336+00:00
-- url     : https://prove2.me/theorems/661f0b41-f230-4bd9-bfa1-6481fced9c62
-- title:
--   Lemma 2 — polynomial marginal bounds on $q_w$ and $\theta_w$
-- statement:
--   Suppose $\bar w_i\le w_i\le2\bar w_i$ for every $i$. Then, for every $(m-1)$-set $U$ and $i\notin U$,
--   $$q_w(i\mid U)\ge\frac{\theta_{\bar w}(i)}{2[(K-m+1)\theta_{\bar w}(i)+m(1-\theta_{\bar w}(i))]},\qquad\theta_w(i)\le2\theta_{\bar w}(i).$$
--   These bounds give the feasibility of the recording rates (8).
--
--   Differences from the source:
--   - encoding: positive anchor fixed on p.12 → hypothesis `∀ i, 0 < wbar i`; reason: stated in the setup of Section 3.1
--   - encoding: second inequality stated for i ∉ U → for every arm i; reason: the inequality does not involve U, and every i lies outside some (m-1)-set because m < K, so this is the same claim
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 2, p.12, (6)

import Mathlib
import Definitions.Def_AdvMultiplayer_SetLaw

namespace AdvMultiplayer

/-- **Lemma 2 (polynomial marginal bounds).** Gan, arXiv:2610.05688, Lemma 2, p.12, (6).

**Formalization Note.** The anchor `w̄` is positive, as fixed on p.12, and the conclusion has two
clauses: the lower bound for every `(m-1)`-set `U` and `i ∉ U`, and the inclusion bound for every `i`. -/
theorem lemma_2 (p : Size) (wbar w : Fin p.K → ℝ) (hpos : ∀ i, 0 < wbar i)
    (hle : ∀ i, wbar i ≤ w i ∧ w i ≤ 2 * wbar i) :
    (∀ U ∈ Finset.powersetCard (p.m - 1) (Finset.univ : Finset (Fin p.K)), ∀ i, i ∉ U →
      theta p wbar i / (2 * (((p.K - p.m + 1 : ℕ) : ℝ) * theta p wbar i + p.m * (1 - theta p wbar i)))
        ≤ qw p wbar w U i) ∧
    ∀ i, theta p w i ≤ 2 * theta p wbar i := by sorry

end AdvMultiplayer
