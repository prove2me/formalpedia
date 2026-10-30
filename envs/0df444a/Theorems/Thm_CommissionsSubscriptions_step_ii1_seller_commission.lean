-- Prove2me | Theorems.Thm_CommissionsSubscriptions_step_ii1_seller_commission
-- name    : CommissionsSubscriptions.step_ii1_seller_commission
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:40:09.33872+00:00
-- url     : https://prove2.me/theorems/660bb16d-58af-4347-b92c-607497b79bfa
-- title:
--   Proof of Theorem 1, step (ii-1), (EC.111) — a seller-commission implementation of the same optimum
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. Let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of (7), let $(\theta^b,\theta^s,\eta^b,\eta^s,\pi)$ satisfy (EC.3), let $p_i=\theta^s_i$, and let $\mu^s,\mu^b$ be the subscription fees (EC.104). Then there are seller commission rates $\gamma^s_i\in[0,1]$ with $\gamma^s_ip_i=\mu^s_i$ for every $i$, and under the alternative profile $(\gamma^s,\gamma^b,\mu^s,\mu^b)=(\gamma^s,0,0,\mu^b)$:
--   $$(p,\bar x,\bar q^s,\bar q^b)\in X(\gamma^s,0,0,\mu^b),\qquad V(\gamma^s,0,0,\mu^b)=h(\bar q^s,\bar q^b).$$
--   Replacing seller subscriptions by seller commissions leaves the equilibrium and the revenue unchanged; this is the paper's argument that optimal fees are not unique.
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
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), proof of Theorem 1, step (ii-1), (EC.111), p. ec42

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_InGammaU
import Definitions.Def_CommissionsSubscriptions_IsEquilibrium
import Definitions.Def_CommissionsSubscriptions_revenue
import Definitions.Def_CommissionsSubscriptions_IsOptimal7
import Definitions.Def_CommissionsSubscriptions_KKT7

namespace CommissionsSubscriptions

/-- **A seller-commission implementation of the same optimum, (EC.111).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), proof of Theorem 1, step (ii-1), (EC.111), p. ec42.

Under Assumptions 1–2 and the standing hypotheses of §2, let `(x̄, q̄^s, q̄^b)` be optimal in (7),
`(θ^b, θ^s, η^b, η^s, π)` satisfy (EC.3), `p_i := θ^s_i`, and `µ^s`, `µ^b` be the subscription
fees (EC.104). Then there are seller commissions `γ^s_i ∈ [0,1]` with `γ^s_i p_i = µ^s_i`, and
under the alternative profile `(γ^s, γ^b, µ^s, µ^b) = (γ^s, 0, 0, µ^b)` we have
`(p, x̄, q̄^s, q̄^b) ∈ X(γ^s, 0, 0, µ^b)` and `V(γ^s, 0, 0, µ^b) = h(q̄^s, q̄^b)`.

**Formalization Note.** (EC.104) is stated in `EReal` as in `step_i2_subscription_only`. -/
theorem step_ii1_seller_commission {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : IsOptimal7 M x qs qb)
    (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ)
    (hK : KKT7 M x qs qb θb θs ηb ηs π) :
    ∃ (μs : S → ℝ) (μb : B → ℝ) (γs : S → ℝ),
      (∀ i, ((θs i - μs i : ℝ) : EReal) = Finv (M.Fs i) (qs i / M.s i)) ∧
      (∀ j, ((μb j + θb j : ℝ) : EReal) = Finv (M.Fb j) (1 - qb j / M.b j)) ∧
      (∀ i, γs i ∈ Set.Icc (0 : ℝ) 1 ∧ γs i * θs i = μs i) ∧
      InGammaU ({ gs := γs, gb := 0, ms := 0, mb := μb } : Fees S B) ∧
      IsEquilibrium M { gs := γs, gb := 0, ms := 0, mb := μb } θs x qs qb ∧
      ((revenue M { gs := γs, gb := 0, ms := 0, mb := μb } θs x : ℝ) : EReal) =
        obj7 M qs qb := by sorry

end CommissionsSubscriptions
