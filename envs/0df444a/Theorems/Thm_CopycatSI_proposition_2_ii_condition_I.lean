-- Prove2me | Theorems.Thm_CopycatSI_proposition_2_ii_condition_I
-- name    : CopycatSI.proposition_2_ii_condition_I
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:03.808182+00:00
-- url     : https://prove2.me/theorems/eb7b0149-dd8f-4a1a-afdd-dda8a5cbc4d8
-- title:
--   Proposition 2(ii), Condition I — strategic inventory: the Table 2 equilibrium for $\beta<\beta^*$, $h<h_1(\beta)$ (corrected: Table 2 rows $q_2$, $s_C$, $\pi_C$)
-- statement:
--   Assume no network externality ($\gamma=0$). If $0\le\beta<\beta^*=(\sqrt{73}-5)/6$ and $0\le h<h_1(\beta)$, then under the **dynamic contract** a subgame-perfect equilibrium exists, and every subgame-perfect equilibrium has the outcome of Table 2 and carries inventory $I>0$. With $\Delta=17-13\beta$ the outcome is
--   $$
--   w_1=\frac{9(1-\beta)-h(2-\beta)}{\Delta},\quad w_2=\frac{2}{13}\Bigl(4h+3-\frac{3(h+4)}{\Delta}\Bigr),\quad
--   I=\frac{1}{\Delta}\Bigl(\frac{5-7\beta}{2}-\frac{h(4\beta^2-13\beta+10)}{1-\beta}\Bigr),
--   $$
--   $$
--   q_1=\frac{13-11\beta}{2\Delta}-\frac{h(7\beta^2-23\beta+18)}{2(1-\beta)\Delta},\quad q_2=\frac{3(2-\beta)}{2\Delta}+\frac{h(2-\beta)(5-4\beta)}{2(1-\beta)\Delta},
--   $$
--   $$
--   s_1=\frac{(2-\beta)(h+4)}{2\Delta},\quad s_2=\frac{11-10\beta}{2\Delta}-\frac{h(4\beta^2-13\beta+10)}{2(1-\beta)\Delta},\quad
--   p_1=\frac12\Bigl(1+\frac{9(1-\beta)-h(2-\beta)}{\Delta}\Bigr),\quad p_2=\frac{1}{13}\Bigl(4h+16-\frac{3(h+4)}{\Delta}\Bigr)-\frac{1}{2-\beta},
--   $$
--   $$
--   \pi_S=\frac{1}{2\Delta}\Bigl(9(1-\beta)-2h(2-\beta)+\frac{h^2(3\beta^2-10\beta+8)}{1-\beta}\Bigr),
--   $$
--   $$
--   \pi_R=\frac{118h-155+\beta(350-357h)+\beta^2(309h-290)+\beta^3(87-80h)}{2(13\beta-17)^2(\beta-2)}+\frac{h^2(97\beta^3-437\beta^2+638\beta-304)}{4(13\beta-17)^2(\beta-1)},
--   $$
--   and, for $\beta>0$,
--   $$
--   s_C=\frac{1}{2\Delta}\Bigl(\frac{23-16\beta}{2-\beta}+\frac{h(5-4\beta)}{1-\beta}\Bigr),\quad p_C=\frac{\beta}{26}\Bigl(4h+16-\frac{3(h+4)}{\Delta}\Bigr)-\frac{\beta}{2(2-\beta)},
--   $$
--   $$
--   \pi_C=\frac{\beta}{16(1-\beta)(2-\beta)^2}\Bigl(\frac{2(2-\beta)}{13}\Bigl(4h+3-\frac{3(h+4)}{\Delta}\Bigr)+2(1-\beta)\Bigr)^2.
--   $$
--
--   This is the strategic-inventory equilibrium of Anand, Anupindi and Bassok (2008) extended to copycat competition; at $\beta=0$ it is their equilibrium ($w_1=(9-2h)/17$, $I=(5-20h)/34$).
--
--   **Formalization Note** The game is the one of the definition items `CopycatSI.Model` and `CopycatSI.Game`: demands are Lebesgue measures of sets of types $\theta\in[0,1]$, strategies are functions of the history each player observes, and a subgame-perfect equilibrium requires every action to be optimal at every history. The tables are the right-hand sides only (`MatchesTable1`, `MatchesTable2`).
--
--   Differences from the source:
--   - encoding: hypothesis "no network externality (γ = 0)" → the model is built with γ = 0 (the period-2 brand utility is θ − p₂; no γ parameter); reason: every result of the mission assumes γ = 0; the instances are the same
--   - reading: model conventions left implicit (pp.6–7) → zero production costs; the copycats observe p₂ only; copycat demand is computed from the two prices and is not rationed by the retailer's stock; wholesale prices, orders and retail prices are ≥ 0; unsold units are worth 0; reason: p.7 says "Copycats observe p₂ and set price p_C"; Table 1's w₁ = 1/2 is the monopoly price only at zero cost; the paper never rations demand
--   - reading: "the optimal decisions … are (summarized in / the same as those in) Table X" → a subgame-perfect equilibrium of the game with the move order of p.7 exists, and every subgame-perfect equilibrium has the on-path outcome of Table X; reason: the paper solves the game by backward induction; existence guards against a vacuous equilibrium predicate
--   - reading: "a cutoff value of holding cost h₁ below which the retailer carries inventory" → I > 0 in every equilibrium when β < β*, h < h₁(β); I = 0 in every equilibrium when β > β* or h > h₁(β); reason: p.10: "strategic inventory exists for holding cost below h₁ and vanishes otherwise"; the cutoff is read as an iff
--   - correction: Table 2, q₂ = 3(2−β)/(2(17−13β)) − h(2−β)(5−4β)/(2(1−β)(17−13β)) → q₂ = 3(2−β)/(2(17−13β)) + h(2−β)(5−4β)/(2(1−β)(17−13β)); reason: q₂ = s₂ − I and π_S = w₁q₁ + w₂q₂ hold for the table's own rows only with +; at β = 0, h = 1/10 (Condition I) the printed q₂ = 5/34 while s₂ − I = 7/34; at β = 0 the corrected row is Anand et al.'s (3 + 5h)/17
--   - correction: Table 2, s_C = (1/(17−13β))((13−16β)/(2−β) + h(5−4β)/(1−β)) → s_C = (1/(2(17−13β)))((23−16β)/(2−β) + h(5−4β)/(1−β)) (= p₂/(2(1−β))); reason: at β = 3/10, h = 1/20 (Condition I) the copycat demand at the table's own p₂, p_C is 13063/31178 ≈ 0.41898, the printed value ≈ 0.38893
--   - correction: Table 2, π_C = (β/(8(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 1 − β)² → π_C = (β/(16(1−β)(2−β)²))((2(2−β)/13)(4h + 3 − 3(h+4)/(17−13β)) + 2(1−β))² (= p_C·s_C); reason: at β = 3/10, h = 1/20 p_C·s_C ≈ 0.036865, the printed value ≈ 0.031056; Table 1's π_C obeys the corrected formula, not the printed one
--   - encoding: copycat rows p_C, s_C, π_C for every β ∈ [0, 1) → asserted for 0 < β < 1 only; reason: at β = 0 the copycat valuation is 0, every p_C earns 0 and the rows are undefined (Table 1's s_C = 3/8 at β = 0 is the limit β → 0); the condition excludes only this undefined case
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Proposition 2(ii) and Table 2, Condition I, p.9

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **Proposition 2(ii), Condition I of Table 2** (Jin–Wu–Chen, SSRN 3826955, version of
2023-05-17, p.9). With no network externality (`γ = 0`), if `0 ≤ β < β* = (√73 − 5)/6` and
`0 ≤ h < h₁(β)`, then under the dynamic contract a subgame-perfect equilibrium exists, and every
subgame-perfect equilibrium has the outcome of Table 2 (with the rows `q₂`, `s_C`, `π_C`
corrected, see `MatchesTable2`) and carries inventory `I > 0`.

**Formalization Note** The copycat rows are asserted for `β > 0` only. -/
theorem proposition_2_ii_condition_I (β h : ℝ) (hβ0 : 0 ≤ β) (hβs : β < betaStar)
    (hh : 0 ≤ h) (hh1 : h < h1 β) :
    (∃ σ : DynProfile, σ.IsSPE β (.finite h)) ∧
    ∀ σ : DynProfile, σ.IsSPE β (.finite h) →
      MatchesTable2 β h (σ.outcome β (.finite h)) ∧ 0 < (σ.outcome β (.finite h)).inv := by sorry

end CopycatSI
