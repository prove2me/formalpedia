-- Prove2me | Theorems.Thm_Eliahou1993_rational_approx_bound
-- name    : Eliahou1993.rational_approx_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:49.648358+00:00
-- url     : https://prove2.me/theorems/6bad5544-0dfe-45aa-9006-5ccaade958e3
-- title:
--   Eliahou (1993) Section 4: conditional lower bound $L \ge 17{,}087{,}915$ for $m > 2^{40}$
-- statement:
--   Let $k_1, L, m \in \mathbb{N}$ be natural numbers with $k_1 > 0$ and $m > 2^{40}$. If the rational ratio $L / k_1$ satisfies the logarithmic inequalities
--
--   $$
--   \log_2 3 < \frac{L}{k_1} \le \log_2\!\left(3 + \frac{1}{m}\right) \implies L \ge 17{,}087{,}915.
--   $$
--
--   This numerical approximation lemma encapsulates the continued-fraction analysis of $\log_2 3$ in Section 4 of Eliahou (1993), using the convergents $p_{13}/q_{13} = 301{,}994 / 190{,}537$, $p_{14}/q_{14} = 16{,}785{,}921 / 10{,}590{,}737$, and $p_{15}/q_{15} = 17{,}087{,}915 / 10{,}781{,}274$.
--
--   **Formalization Note** The bound $L \ge 17{,}087{,}915$ is **conditional** on the explicit hypothesis $2^{40} < m$ (`(2 : ℕ) ^ 40 < m`), which is passed as an assumption and not certified on the platform. Stated in the `Eliahou1993` namespace (`Eliahou1993.rational_approx_bound`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, pp. 50–51, Section 4 / Theorem 1.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/ContinuedFractions.lean#L172-L197 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/ContinuedFractions.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Section 4 / Theorem 1.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Real

theorem Eliahou1993.rational_approx_bound {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    17087915 ≤ L := by sorry
