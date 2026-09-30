-- Prove2me | Theorems.Thm_AlgMechDesign_NonOptimal_sType_final_step
-- name    : AlgMechDesign.NonOptimal.sType_final_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:49:29.565699+00:00
-- url     : https://prove2.me/theorems/3410b2ff-cd4e-49da-abdf-39a8eb7884f4
-- title:
--   Theorem 5.6, final step — under s the optimal allocation of t stays optimal and every other allocation costs at least ∞
-- statement:
--   Let $t$ be a positive type vector, $o$ an optimal allocation for $t$, and $M$ a real number with $M \ge t^l_j$ for all $l,j$. Let $s$ be the type vector with $s^i_j = t^i_j$ if $j \in o^i$ and $s^i_j = M$ otherwise. Then:
--
--   1. $g(o,s) = g(o,t)$;
--   2. $o$ is optimal for $s$: $g(o,s) \le g(y,s)$ for every allocation $y$;
--   3. every allocation $y \ne o$ has $g(y,s) \ge M$.
--
--   These are the facts used in the last paragraph of the proof of Theorem 5.6: $g(\mathrm{opt}(t),t) = g(\mathrm{opt}(s),s)$, and an allocation different from $\mathrm{opt}(s)$ gives some agent an "$\infty$ job", which contradicts any finite approximation ratio once $M$ is chosen large enough.
--
--   **Formalization Note** The paper's $\infty$ is the real parameter $M$; item 3 is the formal content of "there exists an agent who is allocated an $\infty$ job".
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 192, proof of Theorem 5.6, last paragraph (after Corollary 5.8)

import Mathlib
import Definitions.Def_AlgMechDesign_NonOptimal_Model

open Finset

namespace AlgMechDesign.NonOptimal

/-- The final step of the proof of Theorem 5.6 (Nisan–Ronen, p. 192). For a positive type vector
`t`, an optimal allocation `o` for `t` and `M` at least every entry of `t`, the type vector
`s = sType t o M` satisfies: `g(o, s) = g(o, t)`; `o` is optimal for `s`; and every allocation
`y ≠ o` gives some agent a task of time `M`, so `g(y, s) ≥ M`. -/
theorem sType_final_step {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (ht : IsType t)
    (o : Fin k → Fin n) (ho : IsOptimalFor t o) (M : ℝ) (hM : ∀ i j, t i j ≤ M) :
    makespan (sType t o M) o = makespan t o ∧ IsOptimalFor (sType t o M) o ∧
      ∀ y : Fin k → Fin n, y ≠ o → M ≤ makespan (sType t o M) y := by sorry

end AlgMechDesign.NonOptimal
