-- Prove2me | Theorems.Thm_BlindNRMLS_lemma_EC_6
-- name    : BlindNRMLS.lemma_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:30.044198+00:00
-- url     : https://prove2.me/theorems/6842a1cb-5507-4e4d-968f-08d546458daf
-- title:
--   Lemma EC.6 — regret decomposition on $I_\mu$
-- statement:
--   On any instance $I_\mu$ with $n\ge d+1$, let $k^*$ maximize $\mu_{1,k}$. For every policy $\phi$,
--   $$
--   \Big(\tfrac12+\mu_{1,k^*}\Big)T-\mathrm{Rev}_{Q_\mu}(\phi)\ge\sum_{k}\mathbb E^\phi_\mu\Big[\sum_{t}\mathbb 1(z_t=k)\Big](\mu_{1,k^*}-\mu_{1,k}),
--   $$
--   where $z_t$ is the frozen action. This converts plays of a suboptimal arm into revenue loss, whatever happens to the inventories.
--
--   Differences from the source:
--   - reading: µ_{1,k*} = max_k {½ + µ_{1,k}} → k* ∈ argmax_k µ_{1,k}; reason: read literally it adds ½ to the value; the proof uses the maximizer
--   - reading: z_t after the stop keeps the action of τ_stop (p.ec50), with no case for τ_stop = 0 → frozen; a policy with no selling period counts no period; reason: the stronger reading, as it counts more periods than the selling horizon
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Lemma EC.6, p.ec51

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Lemma EC.6: on any `I_µ` and for any policy, with `k*` a maximizer of `µ_{1,k}`,
`(1/2 + µ_{1,k*}) T - Rev_{Q_µ}(ϕ) ≥ ∑_k E[∑_t 1(z_t = k)] (µ_{1,k*} - µ_{1,k})`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Lemma EC.6, p.ec51.

**Formalization Note.** The page's "`µ_{1,k*} = max_k {1/2 + µ_{1,k}}`" is a slip for `k* ∈ argmax_k µ_{1,k}`:
read literally it adds `1/2` to the value. `z_t` is the frozen action of p.ec50, which is the stronger
reading, since it counts more periods; a policy with no selling period has no `z_t` and counts none. -/
theorem lemma_EC_6 (T d n K : ℕ) (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (hdn : d + 1 ≤ n)
    (μ₁ μ₂ : Fin K → ℝ) (hμ₁ : ∀ k, |μ₁ k| ≤ 1 / 2) (hμ₂ : ∀ k, |μ₂ k| ≤ 1 / 2)
    (φ : Policy n K) (kstar : Fin K) (hstar : ∀ k, μ₁ k ≤ μ₁ kstar) :
    ∑ k, (∫ h, (frozenCount (hardProblem T b hb n K) h k : ℝ) ∂(historyLaw (hardLaw d μ₁ μ₂) φ T)) *
        (μ₁ kstar - μ₁ k) ≤
      (1 / 2 + μ₁ kstar) * (T : ℝ) - Rev (hardProblem T b hb n K) (hardLaw d μ₁ μ₂) φ := by sorry

end BlindNRMLS
