-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_eq_7
-- name    : ChenSimchiLevi.Additive.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:42:16.489219+00:00
-- url     : https://prove2.me/theorems/8aef7553-7c05-4635-87cd-e6bd4a15a1d8
-- title:
--   (7) — $g_t(y, d_t(y))$ is $k$-concave when the continuation value is
-- statement:
--   Consider the model of Chen and Simchi-Levi (2004) under Assumptions 1–5 (with $c_{T+1} = 0$, $c_t \ge 0$, $k \ge 0$) and additive demand, and fix a period $t \in \{1, \dots, T\}$. Let $V : \mathbb R \to \mathbb R$ be a continuation value (the role of $v_{t+1}$) such that
--
--   1. $V$ is continuous;
--   2. $V$ is $k$-concave, i.e. $-V$ is $k$-convex (Definition 2.1);
--   3. $|V(x)| \le C(1 + |x|^\rho)$ for some constant $C$ and all $x$;
--   4. $g_t(y, d) = R_t(d) - c_t y + \mathbb E\{-h_t(y - d - \beta_t) + V(y - d - \beta_t)\}$ is jointly continuous in $(y, d) \in \mathbb R \times [\underline d_t, \bar d_t]$.
--
--   Then the function
--   $$y \mapsto g_t\big(y, d_t(y)\big) = \max_{d \in [\underline d_t, \bar d_t]} g_t(y, d)$$
--   is $k$-concave. This is inequality (7) of the paper, the inductive step for the first half of Theorem 3.1(c): it combines Lemma 2, the $k$-concavity of the continuation value, the concavity of $R_t$ and the convexity of $h_t$.
--
--   **Formalization Note.** The step is stated for an arbitrary continuation $V$ with the properties the induction hypothesis provides. The maximum is written as a supremum over $[\underline d_t, \bar d_t]$; under hypothesis 4 it is attained.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 890, §3, proof of Theorem 3.1, (7)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_Model

namespace ChenSimchiLevi.Additive

/-- The step (7) of the proof of Theorem 3.1 in Chen–Simchi-Levi (2004), p. 890, for an arbitrary
continuation `V` in place of `v_{t+1}`: under additive demand, if `V` is continuous, `k`-concave and
`O(|x|^ρ)`, and `g_t(y, d)` built from `V` is jointly continuous, then `g_t(y, d_t(y))` is a
`k`-concave function of `y`. -/
theorem eq_7 (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hVcont : Continuous V)
    (hVk : BertsekasKConvex M.k (fun x => -V x))
    (hVgrowth : ∃ C : ℝ, ∀ x : ℝ, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (hcont : ContinuousOn (Function.uncurry (M.gWith V t))
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    BertsekasKConvex M.k (fun y => -M.GstarWith V t y) := by sorry

end ChenSimchiLevi.Additive
