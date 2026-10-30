-- Prove2me | Theorems.Thm_CommissionsSubscriptions_step_i1_demand_lt_mass
-- name    : CommissionsSubscriptions.step_i1_demand_lt_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:36:16.077459+00:00
-- url     : https://prove2.me/theorems/fb8ad408-036b-4752-9f4a-8010f5a960c6
-- title:
--   Proof of Theorem 1, step (i-1) — every equilibrium has $q^b_j<b_j$
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. For every $(\gamma,\mu)\in\Gamma\times\mathcal U$ and every competitive equilibrium $(p,x,q^s,q^b)\in X(\gamma,\mu)$,
--   $$q^b_j<b_j\qquad\text{for every buyer type }j.$$
--   In equilibrium some buyers of every type stay out of the market. The proof of Theorem 1 uses this to identify the marginal buyer's value $F^{-1}_{b_j}(1-q^b_j/b_j)$ with the cheapest effective price plus $\mu^b_j$ whenever $q^b_j>0$.
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}} in (2b) and argmin in (2d) → minCost: ℝ-infimum over the neighbour subtype; i ∉ argmin written as (1 + γ^b_j)p_i + c_i ≠ minCost (Reading 7); reason: the neighbour set is finite and nonempty (every type has degree ≥ 1, in MarketHyp), so the infimum is the minimum
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), proof of Theorem 1, step (i-1), p. ec39 (unnumbered; equality (a) of (EC.101))

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_InGammaU
import Definitions.Def_CommissionsSubscriptions_IsEquilibrium

namespace CommissionsSubscriptions

/-- **Every equilibrium leaves some buyers out: `q^b_j < b_j`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), proof of Theorem 1, step (i-1), p. ec39 (unnumbered; "given that `q^b_j < b_j`
(Proposition EC.1 (v))", used for equality (a) of (EC.101)).

Under Assumptions 1–2 and the standing hypotheses of §2, for every `(γ, µ) ∈ Γ × U` and every
competitive equilibrium `(p, x, q^s, q^b) ∈ X(γ, µ)`, `q^b_j < b_j` for every buyer type `j`. -/
theorem step_i1_demand_lt_mass {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M) (f : Fees S B)
    (hf : InGammaU f) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (h : IsEquilibrium M f p x qs qb) :
    ∀ j, qb j < M.b j := by sorry

end CommissionsSubscriptions
