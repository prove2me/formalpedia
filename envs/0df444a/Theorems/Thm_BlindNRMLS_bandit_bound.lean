-- Prove2me | Theorems.Thm_BlindNRMLS_bandit_bound
-- name    : BlindNRMLS.bandit_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:31.427134+00:00
-- url     : https://prove2.me/theorems/d2f91f20-316f-4368-81b2-e99ebc30f0f0
-- title:
--   Proof of Theorem 4, p.ec62 — $R^\phi(T)\ge R^\phi_s(T)\ge C_{\mathrm{MAB}}\sqrt{KT}$
-- statement:
--   There is a numerical constant $C_{\mathrm{MAB}}>0$ such that, on the hard problem with $K\ge2$, $T\ge2K$ and $n\ge d+1$, for every $s$ and every $\phi\in\Phi[s]$,
--   $$
--   R^\phi(T)\ge R^\phi_s(T)\ge C_{\mathrm{MAB}}\sqrt{KT}.
--   $$
--   This covers the range of $\nu$ where the cover-time argument gives nothing.
--
--   Differences from the source:
--   - reading: "always holds" → under T ≥ 2K and K ≥ 2; reason: the proof's standing range: for K ≫ T² the claim is false as regret ≤ T, and for K = 1 the regret is 0
--   - generalization: B_i/T ∈ [b,1] and K ≥ 2(d+1) → b_i ≥ 0 arbitrary and K ≥ 2; reason: the sup over Q contains laws with zero demand on products 2,…,n, where inventories play no part
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
--   - generalization: clairvoyant policies have the signature R^d × [s] × [T] → Δ([K]) → clairvoyant policies are all history-dependent policies with at most s switches a.s. under that Q; reason: this class contains the page's, and the signature omits the last action, which a switch-limited policy must know
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, proof of Theorem 4, before (EC.55), pp.ec62–ec63

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- The bandit bound: there is a numerical `C > 0` such that on the hard problem, for `K ≥ 2`,
`T ≥ 2K`, any `s` and `ϕ ∈ Φ[s]`, `R^ϕ(T) ≥ R^ϕ_s(T) ≥ C √(KT)`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, proof of Theorem 4, before (EC.55), p.ec62.

**Formalization Note.** "Always" is the proof's standing `T ≥ 2K`: for `K ≫ T²` the claim is false, as the
regret is at most `T`. `K ≥ 2` excludes the one-armed case, where the regret is `0`. The inventories
may be any nonnegative `b_i T`. -/
theorem bandit_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T d n K : ℕ) (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (s : ℕ) (φ : Policy n K),
        2 ≤ K → 2 * K ≤ T → d + 1 ≤ n → φ ∈ LearningClass (hardProblem T b hb n K) s →
        switchRegret (hardProblem T b hb n K) s φ ≤ regret (hardProblem T b hb n K) φ ∧
        C * Real.sqrt ((K : ℝ) * (T : ℝ)) ≤ switchRegret (hardProblem T b hb n K) s φ := by sorry

end BlindNRMLS
