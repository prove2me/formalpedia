-- Prove2me | Theorems.Thm_CopycatSI_proposition_1
-- name    : CopycatSI.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:47:00.388594+00:00
-- url     : https://prove2.me/theorems/9620eb69-d2bb-4175-9ca7-c9684f8b6800
-- title:
--   Proposition 1 — with $\gamma=0$ and $h=\infty$, both contracts give the Table 1 equilibrium
-- statement:
--   Let $0\le\beta<1$ be the copycat quality, with no network externality ($\gamma=0$) and a prohibitively high holding cost ($h=\infty$, so the retailer cannot carry inventory). Then under the **commitment contract** and under the **dynamic contract**:
--
--   1. a subgame-perfect equilibrium exists, and
--   2. every subgame-perfect equilibrium has the outcome of Table 1:
--   $$
--   (w_1,w_2)=\Bigl(\tfrac12,\tfrac{1-\beta}{2-\beta}\Bigr),\quad (s_1,s_2,s_C)=\Bigl(\tfrac14,\tfrac14,\tfrac{3}{4(2-\beta)}\Bigr),\quad (p_1,p_2)=\Bigl(\tfrac34,\tfrac{3(1-\beta)}{2(2-\beta)}\Bigr),
--   $$
--   $$
--   p_C=\tfrac{3\beta(1-\beta)}{4(2-\beta)},\qquad (\pi_S,\pi_R,\pi_C)=\Bigl(\tfrac{4-3\beta}{8(2-\beta)},\tfrac{4-3\beta}{16(2-\beta)},\tfrac{9\beta(1-\beta)}{16(2-\beta)^2}\Bigr),
--   $$
--   the copycat entries for $\beta>0$.
--
--   In particular the two contracts lead to the same equilibrium outcomes. This is the benchmark against which strategic inventory is measured in Proposition 2.
--
--   **Formalization Note** The game is the one of the definition items `CopycatSI.Model` and `CopycatSI.Game`: demands are Lebesgue measures of sets of types $\theta\in[0,1]$, strategies are functions of the history each player observes, and a subgame-perfect equilibrium requires every action to be optimal at every history. The tables are the right-hand sides only (`MatchesTable1`, `MatchesTable2`).
--
--   Differences from the source:
--   - encoding: hypothesis "no network externality (γ = 0)" → the model is built with γ = 0 (the period-2 brand utility is θ − p₂; no γ parameter); reason: every result of the mission assumes γ = 0; the instances are the same
--   - encoding: h = ∞ → Holding.infinite: units left over after period 1 are lost and no holding cost is paid; reason: the paper's own gloss "the retailer cannot hold inventory (h = ∞)", p.12; ∞ is not a real number
--   - reading: model conventions left implicit (pp.6–7) → zero production costs; the copycats observe p₂ only; copycat demand is computed from the two prices and is not rationed by the retailer's stock; wholesale prices, orders and retail prices are ≥ 0; unsold units are worth 0; reason: p.7 says "Copycats observe p₂ and set price p_C"; Table 1's w₁ = 1/2 is the monopoly price only at zero cost; the paper never rations demand
--   - reading: "the optimal decisions … are (summarized in / the same as those in) Table X" → a subgame-perfect equilibrium of the game with the move order of p.7 exists, and every subgame-perfect equilibrium has the on-path outcome of Table X; reason: the paper solves the game by backward induction; existence guards against a vacuous equilibrium predicate
--   - encoding: copycat rows p_C, s_C, π_C for every β ∈ [0, 1) → asserted for 0 < β < 1 only; reason: at β = 0 the copycat valuation is 0, every p_C earns 0 and the rows are undefined (Table 1's s_C = 3/8 at β = 0 is the limit β → 0); the condition excludes only this undefined case
-- source:
--   Jin–Wu–Chen, Managing Competition from Within and Outside: Using Strategic Inventory and Network Externality to Combat Copycats, SSRN 3826955 (version of 2023-05-17), Proposition 1, p.7; Table 1, p.8

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace CopycatSI

/-- **Proposition 1** (Jin–Wu–Chen, *Managing Competition from Within and Outside*, SSRN 3826955,
version of 2023-05-17, p.7; Table 1, p.8). With no network externality (`γ = 0`) and a
prohibitively high holding cost (`h = ∞`), for every copycat quality `0 ≤ β < 1`: under the
commitment contract and under the dynamic contract a subgame-perfect equilibrium exists, and every
subgame-perfect equilibrium has the outcome of Table 1. In particular the two contracts lead to the
same equilibrium outcomes.

**Formalization Note** `h = ∞` is `Holding.infinite`: units left over after period 1 are lost.
The copycat rows of Table 1 are asserted for `β > 0` only (see `MatchesTable1`). Zero production
costs; the copycats observe `p₂` only; their demand is not rationed by the retailer's stock. -/
theorem proposition_1 (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ((∃ σ : CommitProfile, σ.IsSPE β .infinite) ∧
      ∀ σ : CommitProfile, σ.IsSPE β .infinite →
        MatchesTable1 β (σ.outcome β .infinite)) ∧
    ((∃ σ : DynProfile, σ.IsSPE β .infinite) ∧
      ∀ σ : DynProfile, σ.IsSPE β .infinite →
        MatchesTable1 β (σ.outcome β .infinite)) := by sorry

end CopycatSI
