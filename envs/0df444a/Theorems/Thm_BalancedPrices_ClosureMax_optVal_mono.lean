-- Prove2me | Theorems.Thm_BalancedPrices_ClosureMax_optVal_mono
-- name    : BalancedPrices.ClosureMax.optVal_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:17.470266+00:00
-- url     : https://prove2.me/theorems/7b127417-bffd-4fa3-9b8a-3236ab000418
-- title:
--   Proof of Theorem 5.3, p. 560 — optimal welfare is monotone under valuation dominance
-- statement:
--   Let every valuation in the base spaces $V_i$ take values in $[0,1]$. Let $\tilde v\in V$ and $v\in V^{\max}$ with $\tilde v_i(x_i)\le v_i(x_i)$ for every agent $i$ and outcome $x_i$. Then for every set $S$ of outcome profiles
--   $$\tilde v(\operatorname{OPT}(\tilde v,S))\le v(\operatorname{OPT}(v,S)).$$
--
--   In the proof of Theorem 5.3 this is the comparison $\tilde v(\operatorname{OPT}(\tilde v,\mathcal F_x))\le v(\operatorname{OPT}(\tilde v,\mathcal F_x))\le v(\operatorname{OPT}(v,\mathcal F_x))$, used in both chains.
--
--   **Formalization Note** The optimal value is the real supremum of welfare over $S$, so the paper's two steps (evaluate $v$ at $\tilde v$'s maximiser, then compare with $v$'s optimum) merge into one supremum comparison and no attainment is assumed. The $[0,1]$ bound of §2 keeps both suprema bounded; both sides are $0$ when $S$ is empty. Agents are indexed from zero.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 560, proof of Theorem 5.3, property (b), last two inequalities

import Mathlib
import Definitions.Def_BalancedPrices_ClosureMax_Composition

namespace BalancedPrices.ClosureMax

/-- The supremum comparison used in the proof of Theorem 5.3, including the empty set. -/
theorem optVal_mono {n : ℕ} {X : Fin n → Type*}
    (Vsp : ∀ i, Set (X i → ℝ))
    (hV : ∀ i (f : X i → ℝ), f ∈ Vsp i → ∀ xi, 0 ≤ f xi ∧ f xi ≤ 1)
    (vt vf : BalancedPrices.Extension.Valuation X) (hvt : ∀ i, vt i ∈ Vsp i)
    (hvf : ∀ i, vf i ∈ VmaxSet Vsp i)
    (hle : ∀ i xi, vt i xi ≤ vf i xi)
    (S : Set (BalancedPrices.Extension.Outcome X)) : BalancedPrices.Extension.optVal vt S ≤ BalancedPrices.Extension.optVal vf S := by sorry

end BalancedPrices.ClosureMax
