-- Prove2me | Theorems.Thm_CopycatSI_proposition_2
-- name    : CopycatSI.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:03.349638+00:00
-- url     : https://prove2.me/theorems/ed8828e1-b9e9-49b7-bbb7-c83e613cd030
-- title:
--   Proposition 2 — copycats deter strategic inventory: the equilibria of both contracts and the cutoff $h_1$ (corrected: Table 2 rows $q_2$, $s_C$, $\pi_C$)
-- statement:
--   Suppose there is no network externality ($\gamma=0$). Let $0\le\beta<1$ be the copycat quality and $h\ge 0$ the retailer's unit holding cost, and let $\beta^*=(\sqrt{73}-5)/6\approx 0.5907$ and
--   $$
--   h_1(\beta)=\frac{1-\beta}{(2-\beta)(4-3\beta)}\Bigl(2-\beta-\frac{\beta}{2}\sqrt{\frac{17-13\beta}{1-\beta}}\Bigr).
--   $$
--
--   1. **Commitment contract.** A subgame-perfect equilibrium exists, and every one has the outcome of Table 1.
--   2. **Dynamic contract.** A subgame-perfect equilibrium exists, and
--      - if $\beta<\beta^*$ and $h<h_1(\beta)$, every one has the outcome of Table 2 (rows $q_2$, $s_C$, $\pi_C$ corrected) and carries strategic inventory $I>0$;
--      - if $\beta>\beta^*$ or $h>h_1(\beta)$, every one has the outcome of Table 1 and carries no inventory;
--      - if $\beta\le\beta^*$ and $h=h_1(\beta)$, some one has the Table 1 outcome with $I=0$, and every one has the Table 1 outcome with $I=0$ or the Table 2 outcome.
--   3. **The cutoff.** $h_1(\beta)>0$ for every $0\le\beta<\beta^*$, and $h_1$ is strictly decreasing on $[0,\beta^*]$.
--
--   Table 1 is $(w_1,w_2)=(\tfrac12,\tfrac{1-\beta}{2-\beta})$, $(s_1,s_2,s_C)=(\tfrac14,\tfrac14,\tfrac{3}{4(2-\beta)})$, $(p_1,p_2)=(\tfrac34,\tfrac{3(1-\beta)}{2(2-\beta)})$, $p_C=\tfrac{3\beta(1-\beta)}{4(2-\beta)}$, $(\pi_S,\pi_R,\pi_C)=(\tfrac{4-3\beta}{8(2-\beta)},\tfrac{4-3\beta}{16(2-\beta)},\tfrac{9\beta(1-\beta)}{16(2-\beta)^2})$; Table 2 is the closed form of the definition `CopycatSI.ClosedForms` (Condition I of the paper's Table 2). The copycat entries of both tables are asserted for $\beta>0$.
--
--   The result extends Anand, Anupindi and Bassok (2008), who found strategic inventory under the dynamic contract iff $h<1/4$ without copycats: copycat competition lowers the cutoff and removes strategic inventory altogether once $\beta\ge\beta^*$.
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
--   - reading: "a cutoff value of holding cost h₁ below which the retailer carries inventory" → I > 0 in every equilibrium when β < β*, h < h₁(β); I = 0 in every equilibrium when β > β* or h > h₁(β); reason: p.10: "strategic inventory exists for holding cost below h₁ and vanishes otherwise"; the cutoff is read as an iff
--   - reading: Condition II (h ≥ h₁, or β ≥ β*): "Same as Table 1" → Table 1 with I = 0 in every equilibrium when β > β* or h > h₁(β); on the boundary β ≤ β*, h = h₁(β) some equilibrium has Table 1 with I = 0 and every equilibrium has Table 1 with I = 0 or Table 2; reason: at h = h₁ the supplier's two strategies give the same profit (p.10), so both paths are equilibria; at β = β*, h = h₁(β*) = 0 the Table 2 path has I ≈ 0.046 > 0 and the same π_S (4 − 5β* − 3β*² = 0)
--   - reading: "h₁ is decreasing in β" → h₁ is strictly decreasing on [0, β*]; reason: β* is where h₁ reaches 0 and stops being a cutoff; the formula is not monotone on [0, 1); strict decrease is the stronger reading
--   - encoding: "h₁ > 0 for all β < (√73 − 5)/6" → for all 0 ≤ β < β*; reason: β ≥ 0 is the model's domain (copycat valuation βθ, p.6); there are no other instances
--   - encoding: copycat rows p_C, s_C, π_C for every β ∈ [0, 1) → asserted for 0 < β < 1 only; reason: at β = 0 the copycat valuation is 0, every p_C earns 0 and the rows are undefined (Table 1's s_C = 3/8 at β = 0 is the limit β → 0); the condition excludes only this undefined case
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Proposition 2, p.9, with Table 1 (p.8) and Table 2 (p.9)

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **Proposition 2** (Jin–Wu–Chen, *Managing Competition from Within and Outside*, SSRN 3826955,
version of 2023-05-17, p.9, with Tables 1 and 2, pp.8–9). Suppose there is no network externality
(`γ = 0`). For every copycat quality `0 ≤ β < 1` and holding cost `h ≥ 0`:

(i) under the commitment contract a subgame-perfect equilibrium exists, and every one has the
outcome of Table 1;

(ii) under the dynamic contract a subgame-perfect equilibrium exists, and
* if `β < β* = (√73 − 5)/6` and `h < h₁(β)` (Condition I), every one has the outcome of Table 2
  (rows `q₂`, `s_C`, `π_C` corrected) and carries inventory `I > 0`;
* if `β > β*` or `h > h₁(β)` (Condition II off its boundary), every one has the outcome of
  Table 1 and carries no inventory;
* if `β ≤ β*` and `h = h₁(β)` (the boundary, where the supplier is indifferent), some one has
  the Table 1 outcome with `I = 0`, and every one has the Table 1 outcome with `I = 0` or the
  Table 2 outcome;

and `h₁(β) > 0` for every `0 ≤ β < β*`, and `h₁` is strictly decreasing on `[0, β*]`.

**Formalization Note** Zero production costs; the copycats observe `p₂` only and their demand is
not rationed by the retailer's stock; prices and orders are non-negative. The copycat rows of both
tables are asserted for `β > 0` only (at `β = 0` they are not determined). -/
theorem proposition_2 (β h : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hh : 0 ≤ h) :
    ((∃ σ : CommitProfile, σ.IsSPE β (.finite h)) ∧
      ∀ σ : CommitProfile, σ.IsSPE β (.finite h) →
        MatchesTable1 β (σ.outcome β (.finite h))) ∧
    (∃ σ : DynProfile, σ.IsSPE β (.finite h)) ∧
    (β < betaStar → h < h1 β →
      ∀ σ : DynProfile, σ.IsSPE β (.finite h) →
        MatchesTable2 β h (σ.outcome β (.finite h)) ∧ 0 < (σ.outcome β (.finite h)).inv) ∧
    (betaStar < β ∨ h1 β < h →
      ∀ σ : DynProfile, σ.IsSPE β (.finite h) →
        MatchesTable1 β (σ.outcome β (.finite h)) ∧ (σ.outcome β (.finite h)).inv = 0) ∧
    (β ≤ betaStar → h = h1 β →
      (∃ σ : DynProfile, σ.IsSPE β (.finite h) ∧
        MatchesTable1 β (σ.outcome β (.finite h)) ∧ (σ.outcome β (.finite h)).inv = 0) ∧
      ∀ σ : DynProfile, σ.IsSPE β (.finite h) →
        (MatchesTable1 β (σ.outcome β (.finite h)) ∧ (σ.outcome β (.finite h)).inv = 0) ∨
          MatchesTable2 β h (σ.outcome β (.finite h))) ∧
    (∀ β' : ℝ, 0 ≤ β' → β' < betaStar → 0 < h1 β') ∧
    StrictAntiOn h1 (Set.Icc 0 betaStar) := by sorry

end CopycatSI
