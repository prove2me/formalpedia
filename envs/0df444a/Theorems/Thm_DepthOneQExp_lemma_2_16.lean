-- Prove2me | Theorems.Thm_DepthOneQExp_lemma_2_16
-- name    : DepthOneQExp.lemma_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:44:32.248203+00:00
-- url     : https://prove2.me/theorems/14dd600c-3088-4538-805c-879d606ec602
-- title:
--   Lemma 2.16 (Harrow–Hastings): $\|pA + (1-p)B\| \le 1 - \frac{\varepsilon_B}{12}\min(p\varepsilon_A, 1-p)$
-- statement:
--   Let $\Pi$ be a projector and $A$, $B$ Hermitian operators with $\|A\|,\|B\|\le1$. Suppose there exist $\varepsilon_A,\varepsilon_B\in(0,1)$ such that
--
--   1. $\Pi A = A\Pi = \Pi$;
--   2. $\|(I-\Pi)A(I-\Pi)\|\le 1-\varepsilon_A$;
--   3. $\|\Pi B\Pi\|\le 1-\varepsilon_B$.
--
--   Then for every $p\in(0,1)$,
--   $$
--   \|pA+(1-p)B\| \le 1-\frac{\varepsilon_B}{12}\min(p\,\varepsilon_A,\ 1-p).
--   $$
--
--   This is the combination step of Theorem 2.13: $A$ has a gap off the range of $\Pi$, $B$ has a gap on it, and a convex combination has a gap everywhere.
--
--   **Formalization Note** Operators are complex matrices on a finite index type with the $L^2$ operator norm. The projector is named $P$ in Lean ($\Pi$ is reserved).
--
--   Differences from the source:
--   - reading: "Π a projector" → Π an orthogonal projector (Π² = Π, Πᴴ = Π); reason: in the paper (and [HH09]) a projector is Hermitian; it is applied to Π = Σ_{i≥2}|b_i⟩⟨b_i|
--   - encoding: operators on a Hilbert space → complex matrices on a finite index type with the L² operator norm; reason: the lemma is applied to operators on C^{N²}; finite-dimensional setting of the paper
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Lemma 2.16, Eq. (2.39), p.13 (cited from [HH09, Lemma 1])

import Mathlib

namespace DepthOneQExp

open scoped Matrix.Norms.L2Operator

/-- Lemma 2.16 ([HH09, Lemma 1]) (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on
the unitary group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87,
Lemma 2.16, Eq. (2.39), p.13): let `Π` be a projector and `A, B` Hermitian operators with
`‖A‖, ‖B‖ ≤ 1`, and suppose there are `ε_A, ε_B ∈ (0, 1)` with `ΠA = AΠ = Π`,
`‖(I − Π)A(I − Π)‖ ≤ 1 − ε_A` and `‖ΠBΠ‖ ≤ 1 − ε_B`. Then for every `p ∈ (0, 1)`,
`‖pA + (1 − p)B‖ ≤ 1 − (ε_B/12)·min(p·ε_A, 1 − p)`.

**Formalization Note** Operators are complex matrices on a finite index type with the `L²` operator
norm; "projector" is read as orthogonal projector (`P² = P`, `Pᴴ = P`). The projector is named `P`
(`Π` is reserved in Lean). -/
theorem lemma_2_16 {ι : Type} [Fintype ι] [DecidableEq ι] (P A B : Matrix ι ι ℂ)
    (hP2 : P * P = P) (hPh : P.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1) (εA εB : ℝ) (hεA : εA ∈ Set.Ioo (0 : ℝ) 1)
    (hεB : εB ∈ Set.Ioo (0 : ℝ) 1) (hPA : P * A = P) (hAP : A * P = P)
    (hA' : ‖(1 - P) * A * (1 - P)‖ ≤ 1 - εA) (hB' : ‖P * B * P‖ ≤ 1 - εB)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(p : ℂ) • A + ((1 - p : ℝ) : ℂ) • B‖ ≤ 1 - εB / 12 * min (p * εA) (1 - p) := by sorry

end DepthOneQExp
