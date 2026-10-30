-- Prove2me | Theorems.Thm_CommissionsSubscriptions_step_i2_subscription_only
-- name    : CommissionsSubscriptions.step_i2_subscription_only
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:39:14.213886+00:00
-- url     : https://prove2.me/theorems/73bd00cc-f6cc-40bf-81eb-3575b76ede04
-- title:
--   Proof of Theorem 1, step (i-2), (EC.103)–(EC.110) — a subscription-only implementation of the optimum of (7)
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. Let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of (7) and let $(\theta^b,\theta^s,\eta^b,\eta^s,\pi)$ satisfy (EC.3). Set the prices $p_i=\theta^s_i$ (EC.103), the commissions $\gamma=0$, and the subscription fees (EC.104)
--   $$\mu^s_i=\theta^s_i-F^{-1}_{s_i}\Bigl(\frac{\bar q^s_i}{s_i}\Bigr),\qquad \mu^b_j=F^{-1}_{b_j}\Bigl(1-\frac{\bar q^b_j}{b_j}\Bigr)-\theta^b_j .$$
--   Then these fees are finite, $(0,\mu)\in\Gamma\times\mathcal U$, $(p,\bar x,\bar q^s,\bar q^b)\in X(0,\mu)$, and the platform's revenue in this equilibrium is
--   $$V(0,\mu)=h(\bar q^s,\bar q^b)=\tilde V_{opt}\qquad\text{(EC.110)}.$$
--   So the optimum of (7) is implementable, which gives $V_{opt}\ge\tilde V_{opt}$.
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
--   - encoding: min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}} in (2b) and argmin in (2d) → minCost: ℝ-infimum over the neighbour subtype; i ∉ argmin written as (1 + γ^b_j)p_i + c_i ≠ minCost (Reading 7); reason: the neighbour set is finite and nonempty (every type has degree ≥ 1, in MarketHyp), so the infimum is the minimum
--   - encoding: g′_j, h′_i at the end points defined by footnote 22 as one-sided limits of the derivative; “have finite values” → HasBdryDeriv g L R q d with d : ℝ: HasDerivAt inside (L,R), Tendsto (deriv g) to d from inside at an end point (Reading 8); reason: footnote 22, with the finiteness asserted by Proposition EC.1(iii) built in
--   - encoding: (EC.3g) quantified “∀ i ∈ B” and (EC.3h) “∀ j ∈ S” → (EC.3g) for every j ∈ B, (EC.3h) for every i ∈ S; reason: index typos: the sums are over i (resp. j), so the free index is j ∈ B (resp. i ∈ S)
--   - encoding: µ^s_i = θ^s_i − F⁻¹_{s_i}(q̄^s_i/s_i), µ^b_j = F⁻¹_{b_j}(1 − q̄^b_j/b_j) − θ^b_j (EC.104) → ∃ real µ^s, µ^b with θ^s_i − µ^s_i = F⁻¹_{s_i}(q̄^s_i/s_i) and µ^b_j + θ^b_j = F⁻¹_{b_j}(1 − q̄^b_j/b_j) in EReal; reason: the same fees; the EReal equations also assert that these F⁻¹ values are finite, which the paper uses implicitly
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), proof of Theorem 1, step (i-2), (EC.103)–(EC.110), pp. ec40–ec42

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_InGammaU
import Definitions.Def_CommissionsSubscriptions_IsEquilibrium
import Definitions.Def_CommissionsSubscriptions_revenue
import Definitions.Def_CommissionsSubscriptions_IsOptimal7
import Definitions.Def_CommissionsSubscriptions_KKT7

namespace CommissionsSubscriptions

/-- **The subscription-only implementation of an optimum of (7), (EC.103)–(EC.110).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), proof of Theorem 1, step (i-2), (EC.103)–(EC.110), pp. ec40–ec42.

Under Assumptions 1–2 and the standing hypotheses of §2, let `(x̄, q̄^s, q̄^b)` be optimal in (7)
and `(θ^b, θ^s, η^b, η^s, π)` satisfy (EC.3). Set the prices `p_i := θ^s_i` (EC.103), the
commissions `γ = 0`, and the subscription fees (EC.104)
`µ^s_i = θ^s_i − F⁻¹_{s_i}(q̄^s_i/s_i)`, `µ^b_j = F⁻¹_{b_j}(1 − q̄^b_j/b_j) − θ^b_j`.
Then these fees are real numbers (the `F⁻¹` values are finite), `(0, µ) ∈ Γ × U`,
`(p, x̄, q̄^s, q̄^b) ∈ X(0, µ)`, and the revenue `V(0, µ)` equals `h(q̄^s, q̄^b) = Ṽ_opt` (EC.110).

**Formalization Note.** (EC.104) is stated as `θ^s_i − µ^s_i = F⁻¹_{s_i}(q̄^s_i/s_i)` and
`µ^b_j + θ^b_j = F⁻¹_{b_j}(1 − q̄^b_j/b_j)` in `EReal`; this also asserts that both `F⁻¹` values
are finite, which the paper uses implicitly. -/
theorem step_i2_subscription_only {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : IsOptimal7 M x qs qb)
    (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ)
    (hK : KKT7 M x qs qb θb θs ηb ηs π) :
    ∃ (μs : S → ℝ) (μb : B → ℝ),
      (∀ i, ((θs i - μs i : ℝ) : EReal) = Finv (M.Fs i) (qs i / M.s i)) ∧
      (∀ j, ((μb j + θb j : ℝ) : EReal) = Finv (M.Fb j) (1 - qb j / M.b j)) ∧
      InGammaU ({ gs := 0, gb := 0, ms := μs, mb := μb } : Fees S B) ∧
      IsEquilibrium M { gs := 0, gb := 0, ms := μs, mb := μb } θs x qs qb ∧
      ((revenue M { gs := 0, gb := 0, ms := μs, mb := μb } θs x : ℝ) : EReal) =
        obj7 M qs qb := by sorry

end CommissionsSubscriptions
