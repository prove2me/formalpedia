-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_normalized_main_term_mem_Mb
-- name    : CalibratedCE.Convergence.normalized_main_term_mem_Mb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:31:52.1907+00:00
-- url     : https://prove2.me/theorems/315cbce1-4a6f-458e-8072-9962a58c177b
-- title:
--   Proof of Theorem 1 (p. 45): the $N$-weighted average of the forecasts lies in $M_b(x)$
-- statement:
--   Let $G = (u_1, u_2)$ be a finite two-player game, $R_1$ a best-reply function of player 1, and $f(s)$ a sequence of forecasts, each a probability vector over $S(2)$. Fix $t$ and $a \in S(1)$ and let $P_t(a)$ be the set of forecasts issued in the first $t$ rounds with $R_1(p) = a$. If $\sum_{q \in P_t(a)} N(q, t) > 0$, then
--   $$\sum_{p \in P_t(a)} p \, \frac{N(p, t)}{\sum_{q \in P_t(a)} N(q, t)} \in M_b(a).$$
--
--   The vector is a convex combination of forecasts in $M_p(a) \subseteq M_b(a)$, and it is the normalized main term of the decomposition of $D_t(a, \cdot)$.
--
--   **Formalization Note** The positivity hypothesis (player 1 played $a$ at least once in the first $t$ rounds) is implicit on the page, where the fraction is written without comment.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 45, proof of Theorem 1

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: the `N`-weighted average of the issued forecasts at which player 1
plays `a` lies in `M_b(a)`. -/
theorem normalized_main_term_mem_Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (t : ℕ) (a : Fin m)
    (hpos : 0 < ∑ q ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
      (Shared.N f₁ q t : ℝ)) :
    (fun b => ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
        p b * (Shared.N f₁ p t : ℝ) /
          ∑ q ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a), (Shared.N f₁ q t : ℝ))
      ∈ Mb u₁ a := by sorry

end CalibratedCE.Convergence
