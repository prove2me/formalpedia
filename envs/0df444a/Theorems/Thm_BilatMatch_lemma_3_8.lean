-- Prove2me | Theorems.Thm_BilatMatch_lemma_3_8
-- name    : BilatMatch.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:14:24.380347+00:00
-- url     : https://prove2.me/theorems/901d8d1e-9a9e-4008-ae74-8b76a806260d
-- title:
--   Lemma 3.8 (Auxiliary-Market Reduction) — bilateral bounds on $\mathfrak B\times\mathfrak S_\alpha$ give $V_\alpha(\mathcal J)\ge\beta\,\mathrm{FB}(\mathcal J)$, attained by a normalized mechanism
-- statement:
--   Fix $\alpha,\beta\ge0$, a seller class $\mathfrak S_\alpha$ and a buyer class $\mathfrak B$ as defined before the lemma. Suppose $V_\alpha(F_B,F_S)\ge\beta\,\mathrm{FB}(F_B,F_S)$ for all $F_B\in\mathfrak B$ and $F_S\in\mathfrak S_\alpha$. Then every finite-agent auxiliary matching market $\mathcal J$ with independent buyer priors in $\mathfrak B$, seller priors in $\mathfrak S_\alpha$ and downward-closed feasibility satisfies
--   $$V_\alpha(\mathcal J)\ \ge\ \beta\,\mathrm{FB}(\mathcal J).$$
--   Moreover, this value is attained by an admissible BIC/IIR mechanism that trades only on positive-surplus edges and uses bounded normalized envelope payments, each depending only on the corresponding agent's report.
--
--   **Formalization Note** The auxiliary market's report domains are the finite supports, or the support interval of a regular interval-support seller; $V_\alpha(\mathcal J)$ uses them, the bilateral values use whole-line reports.
--
--   Differences from the source:
--   - reading: this value is attained by a BIC/IIR mechanism → some admissible mechanism, BIC/IIR on the domains, has GFT + α Rev equal to V_α(J) (hence ≥ β FB(J)); reason: the proof uses the normalized optimizer of Lemma 3.6 and App. B.1, which achieves V_α(J); the stronger of the two readings
--   - encoding: conditioning on any positive-mass initial cap → conditioning on any lower set κ of ℝ with positive regularized mass; reason: for a prior carried by its domain, initial subsets of the domain and their lower closures give the same conditional priors
--   - encoding: payments each depending only on the corresponding agent's report → at every domain profile each payment equals the normalized envelope payment at the agent's own report; reason: the envelope payment is a function of the own report only
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma 3.8 and the definitions of 𝔖_α, 𝔅, p.14 (pdf p.16)

import Mathlib
import Definitions.Def_BilatMatch_priorClasses
import Definitions.Def_BilatMatch_envelope
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB

open MeasureTheory

namespace BilatMatch

/-- **Lemma 3.8 (Auxiliary-Market Reduction).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Lemma 3.8 and the definitions of `𝔖_α`, `𝔅` before it, p.14 (pdf p.16).

Fix `α, β ≥ 0`, a seller class `𝔖_α` and a buyer class `𝔅`. Suppose `V_α(F_B, F_S) ≥ β FB(F_B, F_S)`
for all `F_B ∈ 𝔅`, `F_S ∈ 𝔖_α`. Then every finite-agent auxiliary matching market `J` with independent
buyer priors in `𝔅`, seller priors in `𝔖_α` and downward-closed feasibility satisfies
`V_α(J) ≥ β FB(J)`. Moreover, this value is attained by a BIC/IIR mechanism that trades only on
positive-surplus edges and uses bounded normalized envelope payments, each depending only on the
corresponding agent's report.

**Formalization Note**
* The report domains `D` of the auxiliary market are the natural ones (finite supports, or the
  support interval of a regular interval-support seller); `V_α(J)` is `ValphaOn J D α`. The bilateral
  values in the hypothesis use whole-line reports.
* "Attained": the mechanism's `GFT + α Rev` equals `V_α(J)` (hence is at least `β FB(J)`).
* Normalized own-report envelope payments (`IsNormalizedEnvelope`) depend only on the agent's own
  report at every domain profile; boundedness is a uniform bound on all payments at domain
  profiles. -/
theorem lemma_3_8 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (𝔖 𝔅 : Set (Measure ℝ))
    (h𝔖 : IsSellerClass α 𝔖) (h𝔅 : IsBuyerClass 𝔅)
    (hbil : ∀ GB ∈ 𝔅, ∀ GS ∈ 𝔖,
      ((β * (FB (bilateral GB GS)).toReal : ℝ) : EReal) ≤ Valpha (bilateral GB GS) α)
    {B S : Type*} [Fintype B] [Fintype S] (J : Market B S) (hJ : J.IsValid)
    (hJB : ∀ i, J.buyerLaw i ∈ 𝔅) (hJS : ∀ j, J.sellerLaw j ∈ 𝔖) (D : B ⊕ S → Set ℝ)
    (hD : ∀ u, IsNaturalDomain (Sum.elim J.buyerLaw J.sellerLaw u) (D u)) :
    ((β * (FB J).toReal : ℝ) : EReal) ≤ ValphaOn J D α ∧
    ∃ A : Mechanism J, A.Admissible ∧ A.IsBICOn D ∧ A.IsIIROn D ∧
      ((A.GFT + α * A.Rev : ℝ) : EReal) = ValphaOn J D α ∧
      A.PosSurplusOn (domainProfiles D) ∧ A.IsNormalizedEnvelope D ∧
      ∃ K : ℝ, ∀ θ ∈ domainProfiles D, ∀ u, |A.pay θ u| ≤ K := by sorry

end BilatMatch
