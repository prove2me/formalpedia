-- Prove2me | Theorems.Thm_BlindNRMLS_lemma_EC_7
-- name    : BlindNRMLS.lemma_EC_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:29.86845+00:00
-- url     : https://prove2.me/theorems/62e1111a-b434-4595-b591-38508dc9f60f
-- title:
--   Lemma EC.7 (corrected: factor $1+2/T$; the other arms' $\mu_1$ are fixed; plays counted while selling) — shifting one arm's mean
-- statement:
--   Let $k'$ be an arm, $\Delta>0$, and let $\mu,\mu'\in[-\frac12,\frac12]^{2\times K}$ satisfy $\mu'_{1,k'}=\mu_{1,k'}-\Delta$, $\mu'_{1,k}=\mu_{1,k}$ for $k\ne k'$, and $\mu'_{2,k}=\mu_{2,k}$ for all $k$. With $b\in(0,\infty)^d$, $T\ge1$, $n\ge d+1$, every policy $\phi$ satisfies
--   $$
--   \Big(1+\frac2T\Big)J^{\mathrm{DLP}_\mu}-\mathrm{Rev}_{Q_{\mu'}}(\phi)\ge\mathbb E^\phi_{\mu'}\Big[\sum_{t}\mathbb 1(z_t=k')\Big]\Delta,
--   $$
--   where the sum counts the selling periods that post $k'$. It compares a policy under a shifted instance to the LP of the original one.
--
--   Differences from the source:
--   - correction: J^{DLP_µ} − Rev_{Q_µ′}(φ) ≥ … → (1 + 2/T) J^{DLP_µ} − Rev_{Q_µ′}(φ) ≥ …; reason: the proof's Rev_{Q_µ}(φ†) ≤ J^{DLP_µ} fails under the stopping rule: d=1, K=4, n=3, T=4, µ₁=(0,−¼,−½,−½), µ_{2,1}=0.3, µ_{2,2}=−½, φ≡arm 1, k′=2 has J=1.25 and Rev=1.3344
--   - correction: µ′_{2,k′}=µ_{2,k′} and µ′_{2,k}=µ_{2,k} for all k → the second µ′₂ condition, and µ′_{1,k}=µ_{1,k} for k≠k′; reason: the printed conditions repeat themselves and never fix the other arms' µ₁, which the proof needs
--   - correction: z_t with the frozen convention of p.ec50 → z_t counted only while selling, as in the proof's "as long as z_t ∈ [K]"; reason: with frozen actions it is false: d=1, K=2, b=1, µ₁=(½,−½), µ₂=(½,½), k′=1, ∆=1, φ≡arm 1 sells out at T/2, with left side T/2+1 and right side T
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Lemma EC.7, p.ec52

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Lemma EC.7 (corrected): for `I_µ`, `I_µ'` with `µ'_{1,k'} = µ_{1,k'} - ∆`, the other `µ_1`
and all `µ_2` equal, and any policy,
`(1 + 2/T) J^{DLP_µ} - Rev_{Q_µ'}(ϕ) ≥ E^ϕ_µ'[∑_t 1(z_t = k')] ∆`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Lemma EC.7, p.ec52.

**Formalization Note.** The factor `1 + 2/T` is the DLP bound's on this instance: the proof's
`Rev_{Q_µ}(ϕ†) ≤ J^{DLP_µ}` fails under the stopping rule. The hypothesis on the other arms' `µ_1` is
what the page's repeated "`µ'_{2,k} = µ_{2,k}`" leaves out and the proof needs. `∑_t 1(z_t = k')`
counts selling periods only, as in the proof's "as long as `z_t ∈ [K]`"; with the frozen actions of p.ec50
the lemma is false (see the differences of the item). -/
theorem lemma_EC_7 (T d n K : ℕ) (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (hb_pos : ∀ i, 0 < b i)
    (hT : 1 ≤ T) (hdn : d + 1 ≤ n) (μ₁ μ₂ μ₁' μ₂' : Fin K → ℝ)
    (hμ₁ : ∀ k, |μ₁ k| ≤ 1 / 2) (hμ₂ : ∀ k, |μ₂ k| ≤ 1 / 2)
    (hμ₁' : ∀ k, |μ₁' k| ≤ 1 / 2) (hμ₂' : ∀ k, |μ₂' k| ≤ 1 / 2)
    (k' : Fin K) (Δ : ℝ) (hΔ : 0 < Δ) (hk' : μ₁' k' = μ₁ k' - Δ) (hother : ∀ k, k ≠ k' → μ₁' k = μ₁ k)
    (hsame : ∀ k, μ₂' k = μ₂ k) (φ : Policy n K) :
    (∫ h, (soldCount (hardProblem T b hb n K) h k' : ℝ) ∂(historyLaw (hardLaw d μ₁' μ₂') φ T)) * Δ ≤
      (1 + 2 / (T : ℝ)) * J (hardProblem T b hb n K) (hardLaw d μ₁ μ₂) -
        Rev (hardProblem T b hb n K) (hardLaw d μ₁' μ₂') φ := by sorry

end BlindNRMLS
