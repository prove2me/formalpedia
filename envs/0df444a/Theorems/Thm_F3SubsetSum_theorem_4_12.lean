-- Prove2me | Theorems.Thm_F3SubsetSum_theorem_4_12
-- name    : F3SubsetSum.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:02.901209+00:00
-- url     : https://prove2.me/theorems/64b88ca0-4306-4b9c-aaad-9eef025050cc
-- title:
--   Theorem 4.12 — $\Phi_{m,D}$ is surjective except with probability $e^{-m/400}$
-- statement:
--   Let $q\ge3$ be prime, $500n\le m\le n^2$ and $D=\lceil 500n^2/m\rceil$. For $A$ uniform in $\mathbb F_q^{n\times m}$ with columns $a_i$ and $L_i=\langle a_i,x\rangle$,
--
--   $$\Pr\bigl[\Phi_{m,D}:R_{D-2}^m\to R_D,\ (Q_i)\mapsto\textstyle\sum_iL_i^2Q_i\ \text{is not surjective}\bigr]\le e^{-m/400}.$$
--
--   Surjectivity is the only extra failure event of the quotient decoder beyond non-uniqueness, so this theorem gives Theorem 1.7 its exponentially small failure probability.
--
--   Differences from the source:
--   - encoding: D = ⌈500n²/m⌉ → D = ⌈500·n²/m⌉₊, the natural-number ceiling of the real quotient; reason: same value; D is a natural number
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 4.12, p.22 (restated p.23; proof p.24)

import Mathlib
import Definitions.Def_F3SubsetSum_QuotientAlgebra
import Definitions.Def_F3SubsetSum_TruncatedRing

namespace F3SubsetSum

open Classical in
/-- **Theorem 4.12** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 4.12,
p.22; restated p.23; proof p.24): "Assume 500n ≤ m ≤ n² and D = ⌈500n²/m⌉. For a random instance
from Problem 1.5, we have Pr[Φ_{m,D} is not surjective] ≤ e^{−m/400}."

For a fixed prime `q ≥ 3` (Problem 1.5), the fraction of matrices `A ∈ F_q^{n×m}` (uniform) for
which `Φ_{m,D} : R_{D−2}^m → R_D`, `(Q_i) ↦ Σ_i L_i² Q_i` with `L_i = ⟨a_i, x⟩`, is not surjective
is at most `e^{−m/400}`. (`Φ_{m,D}` does not depend on `b`.)

**Formalization Note** `D = ⌈500n²/m⌉` is the natural-number ceiling of the real quotient. -/
theorem theorem_4_12 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n m : ℕ) (h1 : 500 * n ≤ m)
    (h2 : m ≤ n ^ 2) :
    ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
        ¬ Function.Surjective (Phi (ZMod q) q (cols A) ⌈500 * (n : ℝ) ^ 2 / m⌉₊)).card : ℝ) /
        (q : ℝ) ^ (n * m) ≤ Real.exp (-(m : ℝ) / 400) := by sorry

end F3SubsetSum
