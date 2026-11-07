-- Prove2me | Theorems.Thm_ArbSlowFP_theorem_1_1
-- name    : ArbSlowFP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:47.118197+00:00
-- url     : https://prove2.me/theorems/c0a68908-f620-4431-a993-041f3c22e070
-- title:
--   Theorem 1.1 — for every $k\ge2$, a skew-symmetric game with $(k+1)^2-5$ actions, unique best responses after setup, and gap $\Theta(t^{-1/k})$
-- statement:
--   For every integer $k\ge2$ there exist a skew-symmetric matrix $\hat A_k\in\mathbb Q^{n_k\times n_k}$, where
--   $$n_k=(k+1)^2-5,$$
--   and one of its $n_k$ actions designated as the setup action, with the following properties. Simultaneous fictitious play from zero counts in which both players choose the setup action in round $0$ exists. For every such run, at every decision time $t\ge1$ both players have the same unique best response, and their common count vector $z_t$ satisfies
--   $$c\,t^{-1/k}\le\mathrm{Gap}_{\hat A_k}(z_t/t,z_t/t)\le C\,t^{-1/k}\qquad(t\ge1),$$
--   for positive constants $c$, $C$ depending only on the fixed game.
--
--   For $k\ge3$ the exponent is smaller than $1/2$, so Karlin's conjectured $O(t^{-1/2})$ rate fails without any best-response ties, and taking $k$ large shows that no universal polynomial rate holds.
--
--   **Formalization Note** The run is any pair of play sequences satisfying the best-response rule with the prescribed first plays, with a separate clause that one exists. The constants are chosen before the run and before $t$. Best responses are the sets of Lean's `rowBR` and `colBR`, both equal to the same singleton. The matrix is rational, and the run and gap use its cast to the reals.
--
--   Differences from the source:
--   - reading: Gap = Θ(t^{−1/k}) "for each fixed k, with constants depending on the fixed game" → ∃ c C > 0, ∀ t ≥ 1, c·t^{−1/k} ≤ Gap ≤ C·t^{−1/k}; reason: Table 1 on p.4 says "Each rate holds over all integer times up to positive constant factors"; this is at least as strong as the eventual form, and they are equivalent because the gap is positive at every t ≥ 1
--   - encoding: run of (3) with both players choosing the setup action in round 0 → every sequence of plays satisfying (3) with those first plays, together with a clause that one exists; reason: the plays are the data and ties at t = 0 are free; the statement does not assume uniqueness of the run
--   - encoding: Â_k ∈ ℚ^{n_k×n_k}, with run and gap in the reals → A : Matrix (Fin n_k) (Fin n_k) ℚ, with the cast toReal in the run and gap; reason: the score comparisons are the same in ℚ and ℝ; t^{−1/k} needs the reals
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.3, Theorem 1.1, eq. (5)

import Mathlib
import Definitions.Def_ArbSlowFP_IsFPRun

open Matrix

namespace ArbSlowFP

/-- Theorem 1.1, p.3 (Abernethy, Lazarsfeld, Wibisono, arXiv:2610.08768, version of November 3, 2026,
sha256 977c34b6…). For every `k ≥ 2` there is a rational skew-symmetric matrix on `n_k = (k+1)² - 5`
actions with a designated setup action `ω` such that simultaneous fictitious play from zero counts
with both players choosing `ω` in round 0 has the same unique best response for both players at every
`t ≥ 1`, and `Gap(z_t/t, z_t/t) = Θ(t^{-1/k})`.

**Formalization Note.** The statement quantifies over every run with `i₀ = j₀ = ω`, with a separate
clause that one exists. The constants `c`, `C` are chosen before the run and before `t`. `Θ` is read
over all integer `t ≥ 1` (Table 1, p.4: "Each rate holds over all integer times up to positive
constant factors"). The run and the gap use the cast of the matrix to `ℝ`. -/
theorem theorem_1_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (A : Matrix (Fin ((k + 1) ^ 2 - 5)) (Fin ((k + 1) ^ 2 - 5)) ℚ) (ω : Fin ((k + 1) ^ 2 - 5)),
      Aᵀ = -A ∧
      (∃ i j, IsFPRun (toReal A) i j ∧ i 0 = ω ∧ j 0 = ω) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ i j, IsFPRun (toReal A) i j → i 0 = ω → j 0 = ω →
          (∀ t, 1 ≤ t → ∃ a, rowBR (toReal A) (countVec j t) = {a} ∧
            colBR (toReal A) (countVec i t) = {a}) ∧
          (∀ t, countVec i t = countVec j t) ∧
          (∀ t : ℕ, 1 ≤ t →
            c * (t : ℝ) ^ (-(1 / (k : ℝ))) ≤ gap (toReal A) (empirical i t) (empirical j t) ∧
            gap (toReal A) (empirical i t) (empirical j t) ≤
              C * (t : ℝ) ^ (-(1 / (k : ℝ)))) := by sorry

end ArbSlowFP
