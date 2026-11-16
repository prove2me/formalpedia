-- Prove2me | Theorems.Thm_DDNNFNeg_Supplement_theorem_6_1
-- name    : DDNNFNeg.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:50:57.271734+00:00
-- url     : https://prove2.me/theorems/b41f9abb-cfd6-4083-8b7f-68ca3f0a57d3
-- title:
--   Theorem 6.1 (Multi-Partition Lifting Theorem) — $\mathrm{Cov}^m_b(f\circ E) \ge \mathrm{Cov}^{P,Q}_b(f)/(64n)$ for one full-rank $E \in \mathbb F_2^{n\times N}$, $N = O(n)$
-- statement:
--   There is a constant $C > 0$ such that for every sufficiently large $n \in \mathbb N$ there is a full-rank matrix $E \in \mathbb F_2^{n \times N}$ (rank $n$) with $N \le C n$ satisfying the following. For every Boolean function $f : \mathbb F_2^n \to \{0,1\}$, every partition $(P, Q)$ of $[n]$ and every $b \in \{0,1\}$, the function $F : \mathbb F_2^N \to \{0,1\}$, $F(x) = f(Ex)$, satisfies
--
--   $$\mathrm{Cov}^m_b(F) \ \ge\ \frac{\mathrm{Cov}^{P,Q}_b(f)}{64 n}.$$
--
--   Here $\mathrm{Cov}^{P,Q}_b(f)$ is the least number of rectangles with respect to the fixed partition $(P,Q)$ covering $f^{-1}(b)$ exactly, and $\mathrm{Cov}^m_b(F)$ is the least number of rectangles, each with respect to some balanced partition of $[N]$, covering $F^{-1}(b)$ exactly. The theorem turns functions with large fixed-partition cover number into functions with large multi-partition cover number, hence (by Theorem 3.1) large DNNF size.
--
--   **Formalization Note** $C$ is fixed before the threshold and $n$; the matrix $E$ is chosen before $f$, $(P,Q)$ and $b$. $\mathbb F_2^m$ is identified with $\{0,1\}^m$ bitwise. The division is real division.
--
--   Differences from the source:
--   - reading: let n be sufficiently large; N = O(n) → ∃ C > 0, ∃ n₀, ∀ n ≥ n₀, ∃ N ≤ C·n; reason: standard reading of asymptotic notation, the constant fixed before n
--   - generalization: any partition (P, Q) of [n] → any P ⊆ [n] with Q = [n] ∖ P, one part possibly empty; reason: if the source's partitions have nonempty parts, this covers more partitions and specializes to them; with an empty part the bound still holds because E is surjective
--   - encoding: f : F₂ⁿ → {0,1}, F(x) = f(Ex) → f : (Fin n → Bool) → Bool and F = linearLift E f, F₂ᵐ identified with {0,1}ᵐ bitwise; reason: the same functions
--   - encoding: Cov^m_b(F) ≥ Cov^{P,Q}_b(f)/(64n) → (coverNumberFixed P b f : ℝ)/(64·n) ≤ coverNumberMulti b F; reason: real division; the same inequality
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 6.1, p.16 (proof pp.16–17)

import Mathlib
import Definitions.Def_DDNNFNeg_coverNumberMulti
import Definitions.Def_DDNNFNeg_Supplement_coverNumberFixed
import Definitions.Def_DDNNFNeg_Supplement_linearLift

namespace DDNNFNeg.Supplement

/-- **Theorem 6.1** (Multi-Partition Lifting Theorem) (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.16; proof pp.16–17): let `n ∈ ℕ`
be sufficiently large. There exists a full rank matrix `E ∈ 𝔽₂^{n×N}` with `N = O(n)` such
that for every Boolean function `f : 𝔽₂ⁿ → {0,1}`, any partition `(P, Q)` of `[n]`, and any
`b ∈ {0,1}`, the function `F(x) = f(Ex)` satisfies `Cov^m_b(F) ≥ Cov^{P,Q}_b(f) / (64n)`.

**Formalization Note** The constant `C` of `N = O(n)` is fixed before the threshold `n₀` and
`n`. Full rank is rank `n` (so `N ≥ n`). `E` is chosen before `f`, `(P, Q)` and `b`. The partition
`(P, Q)` is encoded by `P : Finset (Fin n)` with `Q = Pᶜ`, and is arbitrary (one part may be
empty). `F` is `linearLift E f`, with `𝔽₂ᵐ` identified with `{0,1}^m` bitwise. The division is
real division, with the explicit `64n` of the paper. -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ N : ℕ, (N : ℝ) ≤ C * n ∧
      ∃ E : Matrix (Fin n) (Fin N) (ZMod 2), E.rank = n ∧
        ∀ (f : (Fin n → Bool) → Bool) (P : Finset (Fin n)) (b : Bool),
          (coverNumberFixed P b f : ℝ) / (64 * n) ≤ (coverNumberMulti b (linearLift E f) : ℝ) := by sorry

end DDNNFNeg.Supplement
