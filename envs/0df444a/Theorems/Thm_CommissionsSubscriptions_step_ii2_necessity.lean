-- Prove2me | Theorems.Thm_CommissionsSubscriptions_step_ii2_necessity
-- name    : CommissionsSubscriptions.step_ii2_necessity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:41:34.740809+00:00
-- url     : https://prove2.me/theorems/14c39907-bd5b-4deb-a8a2-30d9d8f5a340
-- title:
--   Proof of Theorem 1, step (ii-2) — necessity of (8) at an equilibrium that uses the flow $\bar x$
-- statement:
--   Consider a networked market satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. Let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of (7). Let $(\gamma,\mu)\in\Gamma\times\mathcal U$ with $\gamma^s_i<1$ for all $i$ be an optimal commission-subscription pair, and let $p$ be a price vector with
--   $$(p,\bar x,\bar q^s,\bar q^b)\in X(\gamma,\mu).$$
--   Then $p$ satisfies the system (8) with respect to $(\bar x,\bar q^s,\bar q^b)$ and $(\gamma,\mu)$.
--
--   This is the necessity step as the paper argues it, for an equilibrium whose flow is $\bar x$. Theorem 1(ii) applies it to the equilibrium flow of an optimal pair, which is itself an optimal flow of (7).
--
--   Differences from the source:
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
--   - encoding: min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}} in (2b) and argmin in (2d) → minCost: ℝ-infimum over the neighbour subtype; i ∉ argmin written as (1 + γ^b_j)p_i + c_i ≠ minCost (Reading 7); reason: the neighbour set is finite and nonempty (every type has degree ≥ 1, in MarketHyp), so the infimum is the minimum
--   - encoding: V_opt = max over the feasible set of (3) → Vopt: supremum in EReal of (3a) over the feasible set of (3) (Reading 5); reason: attainment of the maximum is stated separately (Theorem 1(i)); the supremum equals the max when it is attained
--   - encoding: (γ, µ) optimal: V(γ, µ) = V_opt, V(γ, µ) the revenue under (γ, µ) → IsOptimalPair: (γ, µ) ∈ Γ × U and some equilibrium under (γ, µ) has revenue V_opt (Reading 4); reason: V(γ, µ) is well defined because equilibria exist (Proposition 1) and all have the same revenue (Corollary 1), both milestones
--   - encoding: (8a)/(8c) “expression − F⁻¹·γ̃ = 0” and (8d) “expression − F⁻¹·γ̃ ≥ 0”, (i,j) ranging over pairs → “expression = F⁻¹·γ̃” and “F⁻¹·γ̃ ≤ expression” in EReal, (i,j) ranging over E; reason: identical on finite values; when the F⁻¹ term is +∞ both forms are false; x̄ is only defined on E
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), proof of Theorem 1, step (ii-2), (EC.112)–(EC.113), pp. ec42–ec43

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_IsOptimalPair
import Definitions.Def_CommissionsSubscriptions_IsOptimal7
import Definitions.Def_CommissionsSubscriptions_System8

namespace CommissionsSubscriptions

/-- **Necessity of (8) at an equilibrium that uses the flow `x̄`.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), proof of Theorem 1, step (ii-2), (EC.112)–(EC.113), pp. ec42–ec43.

Under Assumptions 1–2 and the standing hypotheses of §2, let `(x̄, q̄^s, q̄^b)` be optimal in (7).
Let `(γ, µ)` with `γ^s_i < 1` for all `i` be an optimal commission-subscription pair (so
`(γ, µ) ∈ Γ × U`),
and let `p` be such that `(p, x̄, q̄^s, q̄^b) ∈ X(γ, µ)`. Then `p` satisfies the system (8) with
respect to `(x̄, q̄^s, q̄^b)`.

**Formalization Note.** This is step (ii-2) as the paper argues it: the equilibrium is assumed
to use the flow `x̄` and the supply-demand vector `(q̄^s, q̄^b)`. -/
theorem step_ii2_necessity {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : IsOptimal7 M x qs qb)
    (f : Fees S B) (hgs : ∀ i, f.gs i < 1) (hfopt : IsOptimalPair M f)
    (p : S → ℝ) (heq : IsEquilibrium M f p x qs qb) :
    System8 M x qs qb f p := by sorry

end CommissionsSubscriptions
