-- Prove2me | Theorems.Thm_CommissionsSubscriptions_step_i1_revenue_le_h
-- name    : CommissionsSubscriptions.step_i1_revenue_le_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:37:11.904771+00:00
-- url     : https://prove2.me/theorems/ee46c6d8-8442-4cb2-8c46-81947288c185
-- title:
--   Proof of Theorem 1, step (i-1), (EC.102) — revenue $\le h(q^s,q^b)$ and feasibility in (7)
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. For every $(\gamma,\mu)\in\Gamma\times\mathcal U$ and every competitive equilibrium $(p,x,q^s,q^b)\in X(\gamma,\mu)$:
--
--   1. the platform's revenue is at most $h(q^s,q^b)$:
--   $$\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)p_ix_{ij}+(\mu^s_i+\mu^b_j)x_{ij}\ \le\ \sum_{j\in B}F^{-1}_{b_j}\Bigl(1-\frac{q^b_j}{b_j}\Bigr)q^b_j-\sum_{i\in S}F^{-1}_{s_i}\Bigl(\frac{q^s_i}{s_i}\Bigr)q^s_i-\sum_{i\in S}c_iq^s_i;$$
--   2. $(x,q^s,q^b)$ is feasible in problem (7).
--
--   Together these give $V_{opt}\le\tilde V_{opt}$: problem (7) is a relaxation of problem (3).
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}} in (2b) and argmin in (2d) → minCost: ℝ-infimum over the neighbour subtype; i ∉ argmin written as (1 + γ^b_j)p_i + c_i ≠ minCost (Reading 7); reason: the neighbour set is finite and nonempty (every type has degree ≥ 1, in MarketHyp), so the infimum is the minimum
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), proof of Theorem 1, step (i-1), (EC.101)–(EC.102), pp. ec39–ec40

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_InGammaU
import Definitions.Def_CommissionsSubscriptions_IsEquilibrium
import Definitions.Def_CommissionsSubscriptions_revenue
import Definitions.Def_CommissionsSubscriptions_obj7
import Definitions.Def_CommissionsSubscriptions_Feasible7

namespace CommissionsSubscriptions

/-- **The revenue upper bound (EC.102), and feasibility of equilibria in (7).**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), proof of Theorem 1, step (i-1), (EC.101)–(EC.102), pp. ec39–ec40.

Under Assumptions 1–2 and the standing hypotheses of §2, for every `(γ, µ) ∈ Γ × U` and every
competitive equilibrium `(p, x, q^s, q^b) ∈ X(γ, µ)`:
1. the platform's revenue (3a) is at most `h(q^s, q^b)` of (6):
   `Σ_{(i,j)∈E} (γ^s_i + γ^b_j) p_i x_{ij} + (µ^s_i + µ^b_j) x_{ij} ≤ h(q^s, q^b)` (EC.102);
2. `(x, q^s, q^b)` is feasible in problem (7). -/
theorem step_i1_revenue_le_h {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M) (f : Fees S B)
    (hf : InGammaU f) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (h : IsEquilibrium M f p x qs qb) :
    ((revenue M f p x : ℝ) : EReal) ≤ obj7 M qs qb ∧ Feasible7 M x qs qb := by sorry

end CommissionsSubscriptions
