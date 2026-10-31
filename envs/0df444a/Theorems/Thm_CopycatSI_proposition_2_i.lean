-- Prove2me | Theorems.Thm_CopycatSI_proposition_2_i
-- name    : CopycatSI.proposition_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:00.370602+00:00
-- url     : https://prove2.me/theorems/377b9865-8b59-4dcf-852a-17ef806706f8
-- title:
--   Proposition 2(i) — the commitment contract gives the Table 1 equilibrium for every $h\ge 0$
-- statement:
--   Let $0\le\beta<1$ and let $h\ge 0$ be the retailer's unit holding cost, with no network externality ($\gamma=0$). Under the **commitment contract** a subgame-perfect equilibrium exists, and every subgame-perfect equilibrium has the outcome of Table 1:
--   $$
--   (w_1,w_2)=\Bigl(\tfrac12,\tfrac{1-\beta}{2-\beta}\Bigr),\ (s_1,s_2)=\Bigl(\tfrac14,\tfrac14\Bigr),\ (p_1,p_2)=\Bigl(\tfrac34,\tfrac{3(1-\beta)}{2(2-\beta)}\Bigr),\ (\pi_S,\pi_R)=\Bigl(\tfrac{4-3\beta}{8(2-\beta)},\tfrac{4-3\beta}{16(2-\beta)}\Bigr),
--   $$
--   and, for $\beta>0$, the copycat entries $s_C=\tfrac{3}{4(2-\beta)}$, $p_C=\tfrac{3\beta(1-\beta)}{4(2-\beta)}$, $\pi_C=\tfrac{9\beta(1-\beta)}{16(2-\beta)^2}$.
--
--   So when the supplier commits to both wholesale prices, a finite holding cost changes nothing: the outcome is the benchmark of Proposition 1.
--
--   **Formalization Note** The game is the one of the definition items `CopycatSI.Model` and `CopycatSI.Game`: demands are Lebesgue measures of sets of types $\theta\in[0,1]$, strategies are functions of the history each player observes, and a subgame-perfect equilibrium requires every action to be optimal at every history. The tables are the right-hand sides only (`MatchesTable1`, `MatchesTable2`). No claim is made on the inventory: at $\beta=h=0$ the retailer is indifferent about when to buy her period-2 units.
--
--   Differences from the source:
--   - encoding: hypothesis "no network externality (γ = 0)" → the model is built with γ = 0 (the period-2 brand utility is θ − p₂; no γ parameter); reason: every result of the mission assumes γ = 0; the instances are the same
--   - reading: model conventions left implicit (pp.6–7) → zero production costs; the copycats observe p₂ only; copycat demand is computed from the two prices and is not rationed by the retailer's stock; wholesale prices, orders and retail prices are ≥ 0; unsold units are worth 0; reason: p.7 says "Copycats observe p₂ and set price p_C"; Table 1's w₁ = 1/2 is the monopoly price only at zero cost; the paper never rations demand
--   - reading: "the optimal decisions … are (summarized in / the same as those in) Table X" → a subgame-perfect equilibrium of the game with the move order of p.7 exists, and every subgame-perfect equilibrium has the on-path outcome of Table X; reason: the paper solves the game by backward induction; existence guards against a vacuous equilibrium predicate
--   - encoding: copycat rows p_C, s_C, π_C for every β ∈ [0, 1) → asserted for 0 < β < 1 only; reason: at β = 0 the copycat valuation is 0, every p_C earns 0 and the rows are undefined (Table 1's s_C = 3/8 at β = 0 is the limit β → 0); the condition excludes only this undefined case
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Proposition 2(i), p.9; Table 1, p.8

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **Proposition 2(i)** (Jin–Wu–Chen, SSRN 3826955, version of 2023-05-17, p.9). With no network
externality (`γ = 0`), for every copycat quality `0 ≤ β < 1` and every holding cost `h ≥ 0`:
under the commitment contract a subgame-perfect equilibrium exists, and every subgame-perfect
equilibrium has the outcome of Table 1 (p.8).

**Formalization Note** The copycat rows of Table 1 are asserted for `β > 0` only. No claim is made
on the inventory: at `β = h = 0` the retailer is indifferent about when to buy her period-2 units,
so `I` is not determined. -/
theorem proposition_2_i (β h : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hh : 0 ≤ h) :
    (∃ σ : CommitProfile, σ.IsSPE β (.finite h)) ∧
    ∀ σ : CommitProfile, σ.IsSPE β (.finite h) →
      MatchesTable1 β (σ.outcome β (.finite h)) := by sorry

end CopycatSI
