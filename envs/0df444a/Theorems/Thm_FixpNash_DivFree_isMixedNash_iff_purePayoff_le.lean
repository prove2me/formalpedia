-- Prove2me | Theorems.Thm_FixpNash_DivFree_isMixedNash_iff_purePayoff_le
-- name    : FixpNash.DivFree.isMixedNash_iff_purePayoff_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:06.662153+00:00
-- url     : https://prove2.me/theorems/d9b9773e-e625-442d-ab7d-a2697f515c53
-- title:
--   p. 11 — a profile is a Nash equilibrium iff no switch to a pure strategy pays
-- statement:
--   In a finite game, a profile $x^*$ is a Nash equilibrium when it is a mixed strategy profile and, for every player $i$ and every mixed strategy $y_i$ of player $i$, $u_i(x^*)\ge u_i(y_i;x^*_{-i})$. It suffices to check switches to pure strategies only:
--   $$x^*\text{ is a Nash equilibrium}\iff x^*\in\Delta\ \text{ and }\ u_i((i{:}j);x^*_{-i})\le u_i(x^*)\ \text{ for every player } i \text{ and every } j\in S_i .$$
--   Here $u_i(x^*)$ is player $i$'s expected payoff and $u_i((i{:}j);x^*_{-i})$ the expected payoff when $i$ switches to the pure strategy $j$ while the others keep $x^*$.
--
--   This is the test used in both directions of the characterization of Nash equilibria as fixed points of $G_I$.
--
--   **Formalization Note.** Both sides require $x^*$ to be a mixed profile; the paper's "x∗ is a NE iff …" ranges over strategy profiles. The definition of Nash equilibrium is the published `AGT.IsMixedNash` (deviations to arbitrary lotteries).
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 2.2, p. 11

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- p. 11: a mixed profile is a Nash equilibrium iff no player gains by switching to a
pure strategy: `uᵢ(x) ≥ uᵢ((i:j); x₋ᵢ)` for every player `i` and every `j ∈ Sᵢ`. -/
theorem isMixedNash_iff_purePayoff_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (x : ∀ i, S i → ℝ) :
    AGT.IsMixedNash u x ↔
      AGT.IsMixedProfile x ∧
        ∀ (i : ι) (j : S i),
          DGPNash.NashMap.purePayoff u x i j ≤ AGT.expectedPayoff u x i := by sorry

end FixpNash.DivFree
