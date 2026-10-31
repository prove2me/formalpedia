-- Prove2me | Theorems.Thm_CopycatSI_supplier_profit_continuous
-- name    : CopycatSI.supplier_profit_continuous
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:45.455074+00:00
-- url     : https://prove2.me/theorems/4b50537c-f7f3-442b-af08-f4ca07ba43af
-- title:
--   §3.1, p.10 — the supplier's equilibrium profit is continuous in $(\beta,h)$; at $h=h_1$ his two strategies tie (corrected: Table 2 rows $q_2$, $s_C$, $\pi_C$)
-- statement:
--   Assume no network externality ($\gamma=0$) and consider the **dynamic contract**.
--
--   1. There is a function $f(\beta,h)$, continuous on $\{(\beta,h):0\le\beta<1,\ h\ge 0\}$, such that for every such $(\beta,h)$ a subgame-perfect equilibrium exists and every subgame-perfect equilibrium gives the supplier the profit $\pi_S=f(\beta,h)$.
--   2. For every $0\le\beta<\beta^*$, at the cutoff $h=h_1(\beta)$ there are two subgame-perfect equilibria, one with the outcome of Table 2 (the supplier tolerates the retailer's strategic inventory) and one with the outcome of Table 1 and $I=0$ (he eliminates it), and they give the supplier the same profit.
--
--   Hence, unlike the retailer's profit, the supplier's profit does not jump when the equilibrium switches at $h=h_1$.
--
--   **Formalization Note** The game is the one of the definition items `CopycatSI.Model` and `CopycatSI.Game`: demands are Lebesgue measures of sets of types $\theta\in[0,1]$, strategies are functions of the history each player observes, and a subgame-perfect equilibrium requires every action to be optimal at every history. The tables are the right-hand sides only (`MatchesTable1`, `MatchesTable2`).
--
--   Differences from the source:
--   - encoding: hypothesis "no network externality (γ = 0)" → the model is built with γ = 0 (the period-2 brand utility is θ − p₂; no γ parameter); reason: every result of the mission assumes γ = 0; the instances are the same
--   - reading: model conventions left implicit (pp.6–7) → zero production costs; the copycats observe p₂ only; copycat demand is computed from the two prices and is not rationed by the retailer's stock; wholesale prices, orders and retail prices are ≥ 0; unsold units are worth 0; reason: p.7 says "Copycats observe p₂ and set price p_C"; Table 1's w₁ = 1/2 is the monopoly price only at zero cost; the paper never rations demand
--   - reading: "the optimal decisions … are (summarized in / the same as those in) Table X" → a subgame-perfect equilibrium of the game with the move order of p.7 exists, and every subgame-perfect equilibrium has the on-path outcome of Table X; reason: the paper solves the game by backward induction; existence guards against a vacuous equilibrium predicate
--   - reading: "the supplier's profit … is always continuous in h and β" → the equilibrium supplier profit is a function f(β, h), jointly continuous on {0 ≤ β < 1, h ≥ 0}; reason: joint continuity implies continuity in each variable; it is the stronger reading
--   - correction: Table 2, q₂ = 3(2−β)/(2(17−13β)) − h(2−β)(5−4β)/(2(1−β)(17−13β)) → q₂ = 3(2−β)/(2(17−13β)) + h(2−β)(5−4β)/(2(1−β)(17−13β)); reason: q₂ = s₂ − I and π_S = w₁q₁ + w₂q₂ hold for the table's own rows only with +; at β = 0, h = 1/10 (Condition I) the printed q₂ = 5/34 while s₂ − I = 7/34; at β = 0 the corrected row is Anand et al.'s (3 + 5h)/17
--   - correction: Table 2, s_C = (1/(17−13β))((13−16β)/(2−β) + h(5−4β)/(1−β)) → s_C = (1/(2(17−13β)))((23−16β)/(2−β) + h(5−4β)/(1−β)) (= p₂/(2(1−β))); reason: at β = 3/10, h = 1/20 (Condition I) the copycat demand at the table's own p₂, p_C is 13063/31178 ≈ 0.41898, the printed value ≈ 0.38893
--   - correction: Table 2, π_C = (β/(8(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 1 − β)² → π_C = (β/(16(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 2(1−β))² (= p_C·s_C); reason: at β = 3/10, h = 1/20 p_C·s_C ≈ 0.036865, the printed value ≈ 0.031056; Table 1's π_C obeys the corrected formula, not the printed one
--   - encoding: copycat rows p_C, s_C, π_C for every β ∈ [0, 1) → asserted for 0 < β < 1 only; reason: at β = 0 the copycat valuation is 0, every p_C earns 0 and the rows are undefined (Table 1's s_C = 3/8 at β = 0 is the limit β → 0); the condition excludes only this undefined case
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), §3.1, p.10, second paragraph (last sentence: "The supplier's profit, in contrast, is always continuous in h and β even at the cutoff h = h1 …")

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **§3.1, p.10, second paragraph** (Jin–Wu–Chen, SSRN 3826955, version of 2023-05-17): "the
supplier's profit under dynamic contract is continuous in both h and β … the supplier actively
seeks a switch between two strategies and they generate the same profit for the supplier at
h = h₁".

With no network externality (`γ = 0`):
1. there is a function `f(β, h)`, continuous on `{0 ≤ β < 1, h ≥ 0}`, such that for every such
   `(β, h)` a subgame-perfect equilibrium of the dynamic contract exists and every one gives the
   supplier the profit `π_S = f(β, h)`;
2. for `0 ≤ β < β*` and `h = h₁(β)` there are two subgame-perfect equilibria of the dynamic
   contract, one with the Table 2 outcome and one with the Table 1 outcome and no inventory, and
   they give the supplier the same profit.

**Formalization Note** "Continuous in both h and β" is read as joint continuity in `(β, h)`. -/
theorem supplier_profit_continuous :
    (∃ f : ℝ × ℝ → ℝ,
      ContinuousOn f {x : ℝ × ℝ | 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2} ∧
      ∀ β h : ℝ, 0 ≤ β → β < 1 → 0 ≤ h →
        (∃ σ : DynProfile, σ.IsSPE β (.finite h)) ∧
        ∀ σ : DynProfile, σ.IsSPE β (.finite h) → (σ.outcome β (.finite h)).piS = f (β, h)) ∧
    ∀ β : ℝ, 0 ≤ β → β < betaStar →
      ∃ σ τ : DynProfile,
        σ.IsSPE β (.finite (h1 β)) ∧ MatchesTable2 β (h1 β) (σ.outcome β (.finite (h1 β))) ∧
        τ.IsSPE β (.finite (h1 β)) ∧ MatchesTable1 β (τ.outcome β (.finite (h1 β))) ∧
        (τ.outcome β (.finite (h1 β))).inv = 0 ∧
        (σ.outcome β (.finite (h1 β))).piS = (τ.outcome β (.finite (h1 β))).piS := by sorry

end CopycatSI
