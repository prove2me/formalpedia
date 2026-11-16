-- Prove2me | Theorems.Thm_DistQuantumQuery_Supplement_theorem_8_11
-- name    : DistQuantumQuery.Supplement.theorem_8_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:48:19.314173+00:00
-- url     : https://prove2.me/theorems/b22f13dd-1dbd-4d17-892e-8f387ae8987f
-- title:
--   Theorem 8.11 — distributional XOR lemma: $Q^{\mu^{\otimes k}}_{\frac12-\frac12(2\epsilon)^{k/2}}(f^{\oplus k})\ge\frac{k(1-2\epsilon)}{40\log(1/\epsilon)}Q^\mu_{\frac12-\epsilon}(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, let $f:\Sigma\to\{0,1\}$ be a decision problem and let $\mu$ be a distribution on $\Sigma$. Then for every $\epsilon\in(0,1/2)$ and every integer $k\ge1$,
--   $$
--   Q^{\mu^{\otimes k}}_{\frac12-\frac12(2\epsilon)^{k/2}}\big(f^{\oplus k}\big)\ \ge\ \frac{k(1-2\epsilon)}{40\log_2(1/\epsilon)}\;Q^{\mu}_{\frac12-\epsilon}(f),
--   $$
--   where $f^{\oplus k}(x_1,\dots,x_k):=f(x_1)\oplus\cdots\oplus f(x_k)$ on $\Sigma^k$, $\mu^{\otimes k}$ is the product distribution, and $Q^\mu_\varepsilon$ is the distributional quantum query complexity with error $\varepsilon$.
--
--   Computing the parity of $k$ independent instances with advantage $(2\epsilon)^{k/2}$ thus costs about $k$ times the cost of one instance with advantage $2\epsilon$, up to the factor $(1-2\epsilon)/(40\log_2(1/\epsilon))$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: Σ^k ⊆ {0,1}^{nk}, x = (x_1,…,x_k), μ^{⊗k} → prodDomain S k ⊆ (Fin k × ι → Bool), block i read by blockOf, prodDist μ k = Π_j μ(x_j); reason: the same nk-bit strings queried bit by bit, with positions named (block, bit)
--   - encoding: Q an integer; Ω(·) bounds of real multiples → Q in ℕ∞ cast to ℝ≥0∞, constant as ENNReal.ofReal; reason: same values; no real cast that would send ⊤ to 0
--   - encoding: index register |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential (base Qdist); reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian (base IsProjMeas); reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - reading: log → Real.logb 2 (log₂); reason: the paper fixes log = log₂: §2.3 writes log₂, and the proof of Prop. 8.8 (p.77) converts with ln 2 (log c ≥ (α−β)/(2αd ln 2), 14 ln 2 ≤ 10); the natural log would be a claim the paper does not make
--   - encoding: f^{⊕k}(x_1,…,x_k) = f(x_1) ⊕ ⋯ ⊕ f(x_k) → xorPow f: XOR folded over the blocks 0,…,k−1 from false; enters Q as graphRel; reason: the same Boolean function
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Theorem 8.11, p.79

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_Supplement_prodDomain

open scoped Matrix ENNReal

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

/-- **Theorem 8.11** (distributional XOR lemma; Ben-David, Ebtehaj, *Distributional Quantum Query
Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…, Theorem 8.11, p.79). Let
`Σ ⊂ {0,1}^n`, `f : Σ → {0,1}` a decision problem and `μ` a distribution on `Σ`. Then for
`ε ∈ (0, 1/2)` and `k ≥ 1`,
`Q^{μ^{⊗k}}_{1/2 − (1/2)(2ε)^{k/2}}(f^{⊕k}) ≥ k(1 − 2ε)/(40 log(1/ε)) · Q^μ_{1/2 − ε}(f)`,
where `f^{⊕k}(x_1, …, x_k) := f(x_1) ⊕ ⋯ ⊕ f(x_k)`.

**Formalization Note** `log = log₂` (`Real.logb 2`), the paper's convention (§2.3; the proof of
Proposition 8.8, p.77). `Q` is the base mission's `Qdist` (in `ℕ∞`), cast to `ℝ≥0∞`, and the
constant enters as `ENNReal.ofReal`; the decision problem enters `Q` as `graphRel f`. `Σ^k` is
`prodDomain S k` on the positions `Fin k × ι`, `μ^{⊗k}` is `prodDist μ k`, `f^{⊕k}` is `xorPow f`.
`(2ε)^{k/2}` is the real power. -/
theorem theorem_8_11 {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset (ι → Bool))
    (f : S → Bool) (μ : S → ℝ) (hμ : IsDist μ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal ((k : ℝ) * (1 - 2 * ε) / (40 * Real.logb 2 (1 / ε))) *
        (Qdist S μ (graphRel f) (1 / 2 - ε) : ℝ≥0∞) ≤
      (Qdist (prodDomain S k) (prodDist μ k) (graphRel (xorPow f))
        (1 / 2 - 1 / 2 * (2 * ε) ^ ((k : ℝ) / 2)) : ℝ≥0∞) := by sorry

end DistQuantumQuery.Supplement
