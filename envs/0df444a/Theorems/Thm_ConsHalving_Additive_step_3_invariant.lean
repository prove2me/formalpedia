-- Prove2me | Theorems.Thm_ConsHalving_Additive_step_3_invariant
-- name    : ConsHalving.Additive.step_3_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:43.404722+00:00
-- url     : https://prove2.me/theorems/3b1bb734-335e-463c-b6b2-0acec765ff95
-- title:
--   Proof of Theorem 2.2, p. 5 — one pass of Step 3 keeps a consensus halving, adds a new item j* to T, and items of T stay uncut
-- statement:
--   Let $n$ agents have additive utilities $u_i(j)$ over $m$ items. Suppose that, at the start of a pass of Step 3,
--
--   1. $x$ is a consensus halving;
--   2. every frozen item $j\in T$ is uncut, $x_j\in\{0,1\}$;
--   3. $y$ solves $S\cup T$, i.e. $\sum_j(y_j-\tfrac12)u_i(j)=0$ for every agent $i$ and $y_j=x_j$ for $j\in T$;
--   4. $j^*$ satisfies $y_{j^*}\ne x_{j^*}$ and $\gamma_{j^*}\le\gamma_j$ for every $j$ with $y_j\ne x_j$.
--
--   Let $s=(1-\gamma_{j^*})\,x+\gamma_{j^*}\,y$. Then $s$ is a consensus halving, $j^*\notin T$, and
--   $$s_j\in\{0,1\}\qquad\text{for every } j\in T\cup\{j^*\}.$$
--
--   So the loop invariants (consensus halving, every item of $T$ uncut) survive each pass, and $|T|$ grows by one.
--
--   **Formalization Note** The loop invariants are carried as hypotheses. Utilities are arbitrary reals (the paper remarks on p. 6 that the algorithm also works with negative utilities).
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 5, proof of Theorem 2.2, 'Thus, (x1, …, xm) remains a consensus halving …'

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem step_3_invariant {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x y : Fin m → ℝ) (jstar : Fin m)
    (hx : IsConsensusHalving u x) (hT : ∀ j ∈ T, x j = 0 ∨ x j = 1)
    (hy : SolvesST u T x y) (hstar : y jstar ≠ x jstar)
    (hmin : ∀ j, y j ≠ x j → gamma x y jstar ≤ gamma x y j) :
    IsConsensusHalving u (stepPoint x y (gamma x y jstar)) ∧ jstar ∉ T ∧
      ∀ j ∈ insert jstar T,
        stepPoint x y (gamma x y jstar) j = 0 ∨ stepPoint x y (gamma x y jstar) j = 1 := by sorry

end ConsHalving.Additive
