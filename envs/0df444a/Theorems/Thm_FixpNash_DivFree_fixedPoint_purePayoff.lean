-- Prove2me | Theorems.Thm_FixpNash_DivFree_fixedPoint_purePayoff
-- name    : FixpNash.DivFree.fixedPoint_purePayoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:38.62935+00:00
-- url     : https://prove2.me/theorems/a3c7e559-0079-46e2-815f-08b9524769d0
-- title:
--   Proof of Lemma 20, p. 47 — at a fixed point, u_i((i:j); x_−i) = t_i on the support and ≤ t_i off it
-- statement:
--   Consider a finite game in which every player has a nonempty set of pure strategies, and let $x\in\Delta$ be a mixed profile with $G_I(x)=x$, that is, $x_{ij}=\max(x_{ij}+u_i((i{:}j);x_{-i})-t_i,0)$ for all $i,j$. Then for every player $i$ and every $j\in S_i$:
--   $$x_{ij}>0\implies u_i((i{:}j);x_{-i})=t_i,\qquad\qquad x_{ij}=0\implies u_i((i{:}j);x_{-i})\le t_i .$$
--
--   This is the first half of the proof of Lemma 20: at a fixed point, all strategies in a player's support earn the same payoff $t_i$ and no strategy earns more, which makes $x$ a Nash equilibrium.
--
--   **Formalization Note.** $t_i$ is the threshold of the definition file, the unique root of $f_{i,x}(t)=1$. Every strategy set is assumed nonempty, the paper's tacit assumption.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Section 4, proof of Lemma 20, p. 47

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_FixpNash_DivFree_Map

namespace FixpNash.DivFree

/-- Proof of Lemma 20, p. 47: at a fixed point `x ∈ Δ` of `G_I`,
`uᵢ((i:j); x₋ᵢ) = tᵢ` whenever `xᵢⱼ > 0` and `uᵢ((i:j); x₋ᵢ) ≤ tᵢ` whenever `xᵢⱼ = 0`. -/
theorem fixedPoint_purePayoff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ)
    (hS : ∀ i, Nonempty (S i)) (x : ∀ i, S i → ℝ)
    (hx : AGT.IsMixedProfile x) (hfix : G u x = x) :
    ∀ (i : ι) (j : S i),
      (0 < x i j → DGPNash.NashMap.purePayoff u x i j = threshold u x i) ∧
        (x i j = 0 → DGPNash.NashMap.purePayoff u x i j ≤ threshold u x i) := by sorry

end FixpNash.DivFree
