-- Prove2me | Theorems.Thm_CopycatSI_proposition_2_ii_condition_II
-- name    : CopycatSI.proposition_2_ii_condition_II
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:26.698486+00:00
-- url     : https://prove2.me/theorems/97dcbc4a-33fb-41b1-a5f7-dd99e547a420
-- title:
--   Proposition 2(ii), Condition II — no inventory: the Table 1 equilibrium for $\beta>\beta^*$ or $h>h_1(\beta)$, and the tie at $h=h_1(\beta)$ (corrected: Table 2 rows $q_2$, $s_C$, $\pi_C$)
-- statement:
--   Assume no network externality ($\gamma=0$), $0\le\beta<1$ and $h\ge 0$, and consider the **dynamic contract**.
--
--   1. If $\beta>\beta^*=(\sqrt{73}-5)/6$ or $h>h_1(\beta)$, a subgame-perfect equilibrium exists, and every subgame-perfect equilibrium has the outcome of Table 1 and carries no inventory, $I=0$.
--   2. On the boundary $\beta\le\beta^*$, $h=h_1(\beta)$, some subgame-perfect equilibrium has the outcome of Table 1 with $I=0$, and every subgame-perfect equilibrium has the outcome of Table 1 with $I=0$ or the outcome of Table 2 (rows $q_2$, $s_C$, $\pi_C$ corrected, as in `CopycatSI.ClosedForms`).
--
--   The Table 1 outcome is
--   $$
--   (w_1,w_2)=\Bigl(\tfrac12,\tfrac{1-\beta}{2-\beta}\Bigr),\ (s_1,s_2)=\Bigl(\tfrac14,\tfrac14\Bigr),\ (p_1,p_2)=\Bigl(\tfrac34,\tfrac{3(1-\beta)}{2(2-\beta)}\Bigr),\ (\pi_S,\pi_R)=\Bigl(\tfrac{4-3\beta}{8(2-\beta)},\tfrac{4-3\beta}{16(2-\beta)}\Bigr),
--   $$
--   with, for $\beta>0$, $s_C=\tfrac{3}{4(2-\beta)}$, $p_C=\tfrac{3\beta(1-\beta)}{4(2-\beta)}$, $\pi_C=\tfrac{9\beta(1-\beta)}{16(2-\beta)^2}$. In particular, with copycats of quality above $\beta^*\approx 0.59$ the retailer carries no inventory even when holding is free.
--
--   **Formalization Note** The game is the one of the definition items `CopycatSI.Model` and `CopycatSI.Game`: demands are Lebesgue measures of sets of types $\theta\in[0,1]$, strategies are functions of the history each player observes, and a subgame-perfect equilibrium requires every action to be optimal at every history. The tables are the right-hand sides only (`MatchesTable1`, `MatchesTable2`).
--
--   Differences from the source:
--   - encoding: hypothesis "no network externality (γ = 0)" → the model is built with γ = 0 (the period-2 brand utility is θ − p₂; no γ parameter); reason: every result of the mission assumes γ = 0; the instances are the same
--   - reading: model conventions left implicit (pp.6–7) → zero production costs; the copycats observe p₂ only; copycat demand is computed from the two prices and is not rationed by the retailer's stock; wholesale prices, orders and retail prices are ≥ 0; unsold units are worth 0; reason: p.7 says "Copycats observe p₂ and set price p_C"; Table 1's w₁ = 1/2 is the monopoly price only at zero cost; the paper never rations demand
--   - reading: "the optimal decisions … are (summarized in / the same as those in) Table X" → a subgame-perfect equilibrium of the game with the move order of p.7 exists, and every subgame-perfect equilibrium has the on-path outcome of Table X; reason: the paper solves the game by backward induction; existence guards against a vacuous equilibrium predicate
--   - correction: Table 2, q₂ = 3(2−β)/(2(17−13β)) − h(2−β)(5−4β)/(2(1−β)(17−13β)) → q₂ = 3(2−β)/(2(17−13β)) + h(2−β)(5−4β)/(2(1−β)(17−13β)); reason: q₂ = s₂ − I and π_S = w₁q₁ + w₂q₂ hold for the table's own rows only with +; at β = 0, h = 1/10 (Condition I) the printed q₂ = 5/34 while s₂ − I = 7/34; at β = 0 the corrected row is Anand et al.'s (3 + 5h)/17
--   - correction: Table 2, s_C = (1/(17−13β))((13−16β)/(2−β) + h(5−4β)/(1−β)) → s_C = (1/(2(17−13β)))((23−16β)/(2−β) + h(5−4β)/(1−β)) (= p₂/(2(1−β))); reason: at β = 3/10, h = 1/20 (Condition I) the copycat demand at the table's own p₂, p_C is 13063/31178 ≈ 0.41898, the printed value ≈ 0.38893
--   - correction: Table 2, π_C = (β/(8(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 1 − β)² → π_C = (β/(16(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 2(1−β))² (= p_C·s_C); reason: at β = 3/10, h = 1/20 p_C·s_C ≈ 0.036865, the printed value ≈ 0.031056; Table 1's π_C obeys the corrected formula, not the printed one
--   - reading: Condition II (h ≥ h₁, or β ≥ β*): "Same as Table 1" → Table 1 with I = 0 in every equilibrium when β > β* or h > h₁(β); on the boundary β ≤ β*, h = h₁(β) some equilibrium has Table 1 with I = 0 and every equilibrium has Table 1 with I = 0 or Table 2; reason: at h = h₁ the supplier's two strategies give the same profit (p.10), so both paths are equilibria; at β = β*, h = h₁(β*) = 0 the Table 2 path has I ≈ 0.046 > 0 and the same π_S (4 − 5β* − 3β*² = 0)
--   - reading: "a cutoff value of holding cost h₁ below which the retailer carries inventory" → I > 0 in every equilibrium when β < β*, h < h₁(β); I = 0 in every equilibrium when β > β* or h > h₁(β); reason: p.10: "strategic inventory exists for holding cost below h₁ and vanishes otherwise"; the cutoff is read as an iff
--   - encoding: copycat rows p_C, s_C, π_C for every β ∈ [0, 1) → asserted for 0 < β < 1 only; reason: at β = 0 the copycat valuation is 0, every p_C earns 0 and the rows are undefined (Table 1's s_C = 3/8 at β = 0 is the limit β → 0); the condition excludes only this undefined case
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Proposition 2(ii) and Table 2, Condition II, p.9; §3.1, p.10, first paragraph

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **Proposition 2(ii), Condition II of Table 2** (Jin–Wu–Chen, SSRN 3826955, version of
2023-05-17, p.9). With no network externality (`γ = 0`), `0 ≤ β < 1` and `h ≥ 0`, under the
dynamic contract:
1. if `β > β*` or `h > h₁(β)`, a subgame-perfect equilibrium exists, and every subgame-perfect
   equilibrium has the outcome of Table 1 and carries no inventory (`I = 0`);
2. at the boundary `β ≤ β*`, `h = h₁(β)`, some subgame-perfect equilibrium has the outcome of
   Table 1 with `I = 0`, and every subgame-perfect equilibrium has the outcome of Table 1 with
   `I = 0` or the outcome of Table 2.

**Formalization Note** At `h = h₁(β)` (which, for `β = β*`, is `h = 0`) the supplier is
indifferent between tolerating and eliminating the retailer's inventory (p.10), so a second
equilibrium path, that of Table 2, exists there; the boundary clause therefore asserts a Table 1
equilibrium and that every equilibrium has the Table 1 or the Table 2 outcome. The copycat rows
are asserted for `β > 0` only. -/
theorem proposition_2_ii_condition_II (β h : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hh : 0 ≤ h) :
    (betaStar < β ∨ h1 β < h →
      (∃ σ : DynProfile, σ.IsSPE β (.finite h)) ∧
      ∀ σ : DynProfile, σ.IsSPE β (.finite h) →
        MatchesTable1 β (σ.outcome β (.finite h)) ∧ (σ.outcome β (.finite h)).inv = 0) ∧
    (β ≤ betaStar → h = h1 β →
      (∃ σ : DynProfile, σ.IsSPE β (.finite h) ∧
        MatchesTable1 β (σ.outcome β (.finite h)) ∧ (σ.outcome β (.finite h)).inv = 0) ∧
      ∀ σ : DynProfile, σ.IsSPE β (.finite h) →
        (MatchesTable1 β (σ.outcome β (.finite h)) ∧ (σ.outcome β (.finite h)).inv = 0) ∨
          MatchesTable2 β h (σ.outcome β (.finite h))) := by sorry

end CopycatSI
