-- Prove2me | Theorems.Thm_AdaptiveSparsify_Supplement_theorem_6
-- name    : AdaptiveSparsify.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:54:00.273386+00:00
-- url     : https://prove2.me/theorems/a1beb660-fa97-4838-83fc-f1f3234c63cc
-- title:
--   Theorem 6 — decremental leverage score overestimates of $[A;\kappa^{-1/2}I]$ under adaptive row halving in time $\tilde O(nd+d^{3+\omega})$
-- statement:
--   For every $C_0>0$, $c_\kappa>0$, $c>0$ and every achievable matrix multiplication exponent $\omega_0\ge2$ there are one admissible program $P$ of the randomized barrier-oracle RAM and constants $C>0$, $k\in\mathbb N$ such that the following holds.
--
--   Let $n,d\ge1$, let $0<\kappa\le(n+2)^{c_\kappa}$, and let $A\in\mathbb R^{n\times d}$ have rows with $\|a_i\|_2^2\le\kappa$. The matrix undergoes **row halvings** $a_i\leftarrow a_i/2$, chosen one at a time by an adaptive adversary who sees every estimate published so far, each row being halved at most $C_0\log_2(n+2)$ times. After the initial matrix and after every halving, $P$ publishes estimates $\tilde\tau\in\mathbb R^n$. Then, against every measurable adversary, with probability at least $1-(n+2)^{-c}$:
--
--   1. every published array satisfies, for the current matrix $A$,
--   $$\tilde\tau_i\ge a_i^\top\big(A^\top A+\kappa^{-1}I\big)^{-1}a_i\quad\text{for all }i,\qquad\sum_{i=1}^n\tilde\tau_i\le Cd\big(\log(n+2)\big)^k;$$
--   2. the total work is at most $C\big(nd+d^{3+\omega_0}\big)\big(\log(n+2)\big)^k$, and the run halts once the adversary stops.
--
--   The quantity $a_i^\top(A^\top A+\kappa^{-1}I)^{-1}a_i$ is the leverage score of row $i$ of the stacked matrix $[A;\kappa^{-1/2}I]$. This decremental structure is the engine of Theorem 3: row deletions become $O(\log\kappa)$ halvings, and binary bucketing gives the fully dynamic version.
--
--   **Formalization Note** The game is `AdaptiveSparsify.Supplement.HalvingGame`. A halving past the cap ends the game, with everything published before still required to be correct.
--
--   Differences from the source:
--   - reading: "against an adaptive adversary", randomized, no probability printed → failure at most (n + 2)^{−c} for every c > 0 against every measurable adversary that sees the history of published τ̃, on one event for all clauses, bounded in outer measure; reason: the proof is with high probability (Lemmas 5.5, 5.6, 5.7, Lemma 2.1); reading R2 of the base mission; measurability because the independence argument of pp.37–38 has no content against a non-measurable strategy
--   - reading: "an algorithm" that maintains τ̃ "after every update" → one finite admissible program of the published barrier-oracle RAM; the game snapshots τ̃ (real cells −1 − i) at each yield, one halving per exchange, the first snapshot for the initial matrix; reason: readings R3–R4 of the base mission and the game of the published Theorem 3; the initial estimates are those of Lemma 2.4 (p.33, Definition 5.4)
--   - reading: κ is poly(n) → κ ≤ (n + 2)^{c_κ} with c_κ > 0 chosen before the program, and κ > 0; reason: "poly(n)" fixes the exponent before the instance; no lower bound on κ is imposed
--   - reading: rows undergoing row halving (the number of halvings is not stated in Theorem 6) → a halving that would take a row past C₀ log₂(n + 2) halvings ends the game, with C₀ > 0 chosen first and all earlier snapshots still required to be correct; reason: the standing assumption of §5 used in the proof (Definition 5.4, p.35: "every row is halved for at most O(log n) times"); without any bound no total time bound can hold, since every halving must be read
--   - reading: ω, the matrix multiplication exponent → every ω₀ ≥ 2 achievable on the machine (IsMatMulProgram with constant C_ω); the program and constants may depend on ω₀, C_ω and the multiplication program; reason: ω is an infimum that need not be attained; ω₀ = 3 is achievable, and any faster multiplication program on the machine gives the theorem with its exponent
--   - reading: Õ hides poly-logarithmic factors of n, U, and thus κ → explicit C, k chosen before the instance, with the factor (log(n + 2))^k in the time and in the sum bound; reason: κ ≤ (n + 2)^{c_κ}, so log κ = O(log n); U is not defined in the statement and under either reading (a magnitude bound equal to κ, or the number of updates ≤ C₀ n log₂(n + 2)) its logarithm is O(log n)
--   - encoding: A ∈ ℝ^{n×d} → n ≥ 1, d ≥ 1; reason: at d = 0 the time bound is 0 and no program can run; at n = 0 there is nothing to maintain
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 6, p.32; Definition 5.4, p.35; proof §5, pp.33–39

import Mathlib
import Definitions.Def_AdaptiveSparsify_Supplement_MatMul
import Definitions.Def_AdaptiveSparsify_Supplement_HalvingGame

open Matrix

namespace AdaptiveSparsify

namespace Supplement

/-- **Theorem 6**, p.32 (§5; proof pp.33–39).

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Theorem 6, p.32.

"Let κ be a parameter that is poly(n), and A ∈ R^{n×d} be a matrix with row norms at most κ
(‖a_i‖₂² ≤ κ for all i) undergoing row halving, which is setting a_i to a_i/2. We can maintain in
total time Õ(nd + d^{3+ω}) against an adaptive adversary leverage overestimates τ̃_i of the rows of
[A; κ^{−1/2}I] summing to Õ(d), that is: τ̃_i ≥ a_i⊤(A⊤A + κ⁻¹I)⁻¹a_i after every update.
∑_i τ̃_i ≤ Õ(d), where recall Õ(·) hides poly-logarithmic factors of n, U, and thus κ."

**Formalization Note.** The game is `AdaptiveSparsify.Supplement.HalvingGame` on the published machine:
one program for all `n, d, A, κ` and every measurable adaptive adversary, one snapshot after every
halving. "κ is poly(n)" is `κ ≤ (n + 2)^{c_κ}` with `c_κ` chosen first; §5's standing assumption
(Definition 5.4, p.35) that every row is halved at most `O(log n)` times is the cap `C₀ log₂(n + 2)`,
`C₀` chosen first; a halving past the cap ends the game, with everything published before still
required to be correct. `ω` is any achievable exponent `ω₀ ≥ 2` (`IsMatMulProgram`). The polylog is
`(log(n + 2))^k`. The guarantee holds on one event of probability at least `1 - (n + 2)^{-c}`
(reading R2), bounded in outer measure. -/
theorem theorem_6 : ∀ C₀ : ℝ, 0 < C₀ → ∀ cκ : ℝ, 0 < cκ → ∀ c : ℝ, 0 < c →
    ∀ (ω₀ Cω : ℝ) (Pmul : Program), 2 ≤ ω₀ → Supplement.IsMatMulProgram Pmul ω₀ Cω →
    ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (κ : ℝ) (σ : Supplement.HalvingStrategy n),
        1 ≤ n → 1 ≤ d → 0 < κ → κ ≤ ((n : ℝ) + 2) ^ cκ → (∀ i, A i ⬝ᵥ A i ≤ κ) →
        σ.Measurable →
        tape {ω | ¬ Supplement.HalvingSuccess P σ A κ C₀ ω₀ C k ω} ≤
          ENNReal.ofReal (((n : ℝ) + 2) ^ (-c)) := by sorry

end Supplement

end AdaptiveSparsify
