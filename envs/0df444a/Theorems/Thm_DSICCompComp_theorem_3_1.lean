-- Prove2me | Theorems.Thm_DSICCompComp_theorem_3_1
-- name    : DSICCompComp.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:30:56.141529+00:00
-- url     : https://prove2.me/theorems/cc0034ab-2d4f-49f9-bc22-46af19c2879f
-- title:
--   Theorem 3.1 — selling separately needs $\Omega(\sqrt{nm})$ extra bidders to match the optimal DSIC revenue
-- statement:
--   Let $\mathcal D$ be the set of DSIC/IR mechanisms and $\mathcal A^R_m$ the set of regular $m$-dimensional product distributions. The **selling-separately competition complexity** of $(\mathcal D, \mathcal A^R_m)$,
--   $$
--   \mathrm{SSComp}_{\mathcal D,\mathcal A^R_m}(n) = \inf_{c\in\mathbb N\cup\{0\}}\bigl\{c : \mathrm{SRev}_{n+c}(D) \ge \mathrm{Rev}^{\mathcal D}_n(D)\ \ \forall D \in \mathcal A^R_m\bigr\},
--   $$
--   is $\Omega(\sqrt{nm})$ when $2 \le m \le n$. Explicitly: there are an absolute constant $C > 0$ and a threshold $N_0$ such that for all $n \ge N_0$, all $m$ with $2 \le m \le n$, and every integer $c \ge 0$ with $c < C\sqrt{nm}$, some regular product distribution $D = D_1\times\cdots\times D_m$ satisfies
--   $$
--   \mathrm{SRev}_{n+c}(D) \;<\; \mathrm{Rev}^{\mathcal D}_n(D).
--   $$
--
--   Here $\mathrm{Rev}^{\mathcal D}_n(D)$ is the optimal revenue of a DSIC/IR mechanism with $n$ iid additive bidders and $\mathrm{SRev}_{n+c}(D)$ the revenue of selling each item separately by Myerson's auction to $n + c$ bidders. The theorem says that, even for regular distributions and even against dominant-strategy mechanisms, selling separately needs $\Omega(\sqrt{nm})$ additional bidders, matching the $O(\sqrt{nm})$ upper bound of Beyhaghi and Weinberg against the optimal BIC revenue.
--
--   Differences from the source:
--   - reading: SSComp is Ω(√nm) when 2 ≤ m ≤ n → ∃ C > 0, ∃ N₀ quantified before ∀ n ≥ N₀ and ∀ m with 2 ≤ m ≤ n; reason: the standard meaning of Ω, with absolute constants
--   - reading: SSComp(n) = inf{c : SRev_{n+c}(D) ≥ Rev^𝒟_n(D) ∀ D ∈ 𝒜^R_m} ≥ C√(nm) → every c ∈ ℕ with c < C√(nm) has some regular D with SRev_{n+c}(D) < Rev^𝒟_n(D); reason: equivalent to the infimum bound; avoids sInf ∅ = 0 in ℕ
--   - generalization: 𝒟 = the DSIC/IR mechanisms → the published RevDS class: feasible, DSIC and IR at every profile in ℝ≥0^{n×m}, measurable payments; reason: a smaller class has a smaller supremum Rev^𝒟_n, so the strict inequality is stronger and implies the paper's
--   - reading: regular: φ = v − (1 − F)/f nondecreasing (Section 2), or concave revenue curve (footnote 1) → IsRegular: a density positive and finite on an interval carrying all mass, with φ monotone there; reason: the Section 2 definition with the standard positive-density convention; it is the narrower class, so the ∃ D statement is the stronger reading
--   - encoding: values drawn from D_j on [0, ∞), SRev by Myerson's auction → D_j a probability measure on ℝ≥0; SRev the sum of the one-item optimal DSIC revenues; reason: values are nonnegative; the one-item DSIC optimum is Myerson's revenue
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Theorem 3.1, p.7 (pdf p.8)

import Mathlib
import Definitions.Def_DSICCompComp_IsRegular
import Definitions.Def_DSICCompComp_optRevDSIC
import Definitions.Def_DSICCompComp_sRev

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- Theorem 3.1 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, Theorem 3.1, p.7 (pdf p.8)): let `𝒟` be the set of DSIC/IR mechanisms
and `𝒜^R_m` the set of regular `m`-dimensional product distributions. The Selling Separately
Competition Complexity of `(𝒟, 𝒜^R_m)` is `Ω(√(nm))` when `2 ≤ m ≤ n`.

Lean reading: there are an absolute constant `C > 0` and a threshold `N₀` such that for all
`n ≥ N₀` and all `m` with `2 ≤ m ≤ n`, and every `c ∈ ℕ` with `c < C√(nm)`, some regular product
distribution `D = D_1 × ⋯ × D_m` has `SRev_{n+c}(D) < Rev^𝒟_n(D)`; equivalently
`SSComp_{𝒟,𝒜^R_m}(n) = inf{c : SRev_{n+c}(D) ≥ Rev^𝒟_n(D) ∀ D ∈ 𝒜^R_m} ≥ C√(nm)`.

**Formalization Note** `Ω` with its standard meaning: `C` and `N₀` are quantified before `n` and
`m`. The infimum (Definition 2.1) is unfolded, which avoids `sInf ∅ = 0` in `ℕ`. `Rev^𝒟_n` is the
published `RevDS` (DSIC/IR at every profile in `ℝ≥0`, measurable payments) and `SRev` the sum of
the one-item optima (`sRev`). -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → 2 ≤ m → m ≤ n →
      ∀ c : ℕ, (c : ℝ) < C * Real.sqrt ((n : ℝ) * m) →
        ∃ D : Fin m → ProbabilityMeasure ℝ≥0, (∀ j, IsRegular (D j : Measure ℝ≥0)) ∧
          sRev (n + c) D < optRevDSIC n D := by sorry

end DSICCompComp
