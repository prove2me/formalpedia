-- Prove2me | Theorems.Thm_AgnHalfMem_Supplement_theorem_4_3
-- name    : AgnHalfMem.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:57:25.921204+00:00
-- url     : https://prove2.me/theorems/8fd9204a-a220-45c4-b363-a67901fd2254
-- title:
--   Theorem 4.3 — agnostic learning of $\gamma$-margin halfspaces, $\gamma=c_0\varepsilon/\sqrt d$, needs $\Omega(d/\varepsilon^2)$ bits or $2^{\Omega(1/\varepsilon^2)}$ samples
-- statement:
--   There are constants $C,c_0,\varepsilon_0>0$ and $c>0$ such that the following holds for every dimension $d\ge1$ and every $\varepsilon$ with
--   $$
--   \frac{C}{\sqrt d}\ \le\ \varepsilon\ \le\ \varepsilon_0 .
--   $$
--   Set $\gamma=c_0\varepsilon/\sqrt d$. No randomized streaming algorithm that uses at most $c\,d/\varepsilon^2$ bits of memory (at most $2^{c d/\varepsilon^2}$ states) and at most $2^{c/\varepsilon^2}$ samples agnostically PAC learns halfspaces with $\gamma$-margin to excess error $\varepsilon$ with success probability $2/3$. That is, for some distribution $D$ on $\mathbb R^d\times\{-1,1\}$ with no mass at $x=0$, the probability that the algorithm outputs a classifier $f$ with
--   $$
--   \Pr_{(x,y)\sim D}[f(x)\ne y]\le\mathrm{OPT}_\gamma(D)+\varepsilon
--   $$
--   is less than $2/3$.
--
--   In words, any streaming algorithm for agnostic $\gamma$-margin learning at this margin needs either $\Omega(d/\varepsilon^2)$ bits of memory or $2^{\Omega(1/\varepsilon^2)}$ samples. In the realizable margin setting the perceptron needs only $O(d\log(2/\gamma)+\log(1/\varepsilon))$ bits and $O(1/(\gamma^2\varepsilon))$ samples (Theorem 5.1), so the bound separates agnostic from realizable margin learning.
--
--   **Formalization Note** Algorithms are seeded families of branching programs on an arbitrary seed space, jointly measurable in seed and sample. Memory of $b$ bits means at most $2^b$ states, and one constant $c$ serves both resources.
--
--   Differences from the source:
--   - encoding: "Ω(d/ε²) bits of memory or 2^{Ω(1/ε²)} samples" → one constant c, chosen with C, c₀, ε₀ before d, ε and the algorithm; no algorithm with card S ≤ 2^{c·d/ε²} and (T:ℝ) ≤ 2^{c/ε²} learns; reason: b bits of memory is at most 2^b states; Ω means some positive universal constant, and two constants reduce to their minimum
--   - generalization: "any streaming algorithm" (App. B: deterministic branching programs WLOG) → every seeded family of Definition B.1 programs on any seed space Ω with seed law P; reason: deterministic algorithms are the case of a one-point seed space
--   - encoding: probabilities over the algorithm's randomness and the samples → IsMeasurableAlg A (joint measurability in seed and sample); reason: a probability presupposes measurable events, as in the base mission's Theorem 4.10
--   - encoding: y⟨w,x⟩/‖x‖₂ undefined at x = 0 → the learner is required to succeed on every D with D{x = 0} = 0 (AgnMarginLearns); reason: err_γ(w, D) is defined exactly on these D, and on them optMargin is the printed OPT_γ, so the Lean learner class is the paper's and no instance changes
--   - encoding: labels in {−1,1}, x ∈ ℝ^d, ‖·‖₂, min over unit w, "success probability at least 2/3" → Bool with true ↔ +1, Fin d → ℝ, √(Σ xᵢ²), infimum over Σ wᵢ² = 1, ofReal (2/3) ≤ product measure of the success set; reason: Lean conventions; same instances
--   - encoding: d unrestricted → 0 < d; reason: C/√d is undefined at d = 0; Lean's x/0 = 0 would admit every ε
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 4.3, p.10 (proof pp.10–11)

import Mathlib
import Definitions.Def_AgnHalfMem_StreamAlg
import Definitions.Def_AgnHalfMem_Supplement_AgnMarginLearns

open MeasureTheory

universe u v

namespace AgnHalfMem

namespace Supplement

/-- **Theorem 4.3 (agnostic learning of γ-margin halfspaces).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Theorem 4.3, p.10: "There exist constants C, c0, ε0 > 0 such that
for every C/√d ≤ ε ≤ ε0, setting γ = c0ε/√d, any streaming algorithm that agnostically PAC learns
halfspaces with γ-margin to excess error at most ε, with success probability at least 2/3, must
either use Ω(d/ε²) bits of memory or 2^{Ω(1/ε²)} samples."

There are constants `C, c₀, ε₀ > 0` and `c > 0` such that for every `d ≥ 1` and every `ε` with
`C/√d ≤ ε ≤ ε₀`, with `γ = c₀ε/√d`, no randomized streaming algorithm with at most `2^{c d/ε²}`
memory states (`c d/ε²` bits) and at most `2^{c/ε²}` samples agnostically PAC learns halfspaces
with γ-margin to excess error `ε` with success probability `2/3`.

**Formalization Note.** `Ω(·)` is one explicit constant `c` for both resources, chosen with
`C, c₀, ε₀` before `d`, `ε` and the algorithm. Memory of `b` bits is `Fintype.card S ≤ 2^b`.
Algorithms are seeded families of Definition B.1 programs on any seed space (the base mission's
`StreamAlg`), jointly measurable. `0 < d` excludes the undefined `C/√0`. -/
theorem theorem_4_3 :
    ∃ C c₀ ε₀ c : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < ε₀ ∧ 0 < c ∧
      ∀ (d : ℕ), 0 < d → ∀ ε : ℝ, C / Real.sqrt d ≤ ε → ε ≤ ε₀ →
      ∀ (Ω : Type u) (S : Type v) [MeasurableSpace Ω] [Fintype S] (T : ℕ)
        (A : StreamAlg Ω S (Fin d → ℝ) T) (P : Measure Ω), IsProbabilityMeasure P →
        IsMeasurableAlg A →
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (c * d / ε ^ 2) → (T : ℝ) ≤ (2 : ℝ) ^ (c / ε ^ 2) →
        ¬ AgnMarginLearns (c₀ * ε / Real.sqrt d) ε A P := by sorry

end Supplement

end AgnHalfMem
