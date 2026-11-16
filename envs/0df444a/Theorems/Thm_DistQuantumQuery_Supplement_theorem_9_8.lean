-- Prove2me | Theorems.Thm_DistQuantumQuery_Supplement_theorem_9_8
-- name    : DistQuantumQuery.Supplement.theorem_9_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:49:29.559614+00:00
-- url     : https://prove2.me/theorems/0db542a9-7b95-494a-bc21-6422491af871
-- title:
--   Theorem 9.8 — distributional direct product: $Q^{\mu^{\otimes k}}_{1-\alpha^k}(f^{\otimes k})\ge\frac{k(\alpha-\beta)}{10\alpha\log(2(1-\beta)/(\alpha-\beta))}Q^\mu_{1-\beta}(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, let $f\subseteq\Sigma\times\Omega$ be a search problem, let $\mu$ be a distribution on $\Sigma$, let $\alpha,\beta$ be success parameters with $0<\beta<\alpha<1$, and let $k\ge1$ be an integer. Then
--   $$
--   Q^{\mu^{\otimes k}}_{1-\alpha^k}\big(f^{\otimes k}\big)\ \ge\ \frac{k(\alpha-\beta)}{10\,\alpha\,\log_2\!\big(\tfrac{2(1-\beta)}{\alpha-\beta}\big)}\;Q^{\mu}_{1-\beta}(f),
--   $$
--   where $f^{\otimes k}$ is the $k$-fold problem on $\Sigma^k$ (an output is correct iff it is correct on every block), $\mu^{\otimes k}$ the product distribution and $Q^\mu_\varepsilon$ the distributional quantum query complexity with error $\varepsilon$.
--
--   Solving $k$ independent instances with success probability $\alpha^k$ requires about $k$ times the queries needed for one instance with success $\beta<\alpha$.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: Σ^k ⊆ {0,1}^{nk}, x = (x_1,…,x_k), μ^{⊗k} → prodDomain S k ⊆ (Fin k × ι → Bool), block i read by blockOf, prodDist μ k = Π_j μ(x_j); reason: the same nk-bit strings queried bit by bit, with positions named (block, bit)
--   - encoding: f ⊆ Σ × Ω a search problem (a total relation, standing convention §2.4, p.17) → relation R : Σ → Ω → Prop with hypothesis ∀ x, ∃ s, R x s; reason: the paper's standing assumption stated once at the top of §2.4
--   - encoding: output set Ω → Ω a finite type; reason: measurements have a finite outcome set Ω (§2.3.2, p.16), as in the base Qdist
--   - encoding: Q an integer; Ω(·) bounds of real multiples → Q in ℕ∞ cast to ℝ≥0∞, constant as ENNReal.ofReal; reason: same values; no real cast that would send ⊤ to 0
--   - encoding: index register |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential (base Qdist); reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian (base IsProjMeas); reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - reading: log → Real.logb 2 (log₂); reason: the paper fixes log = log₂: §2.3 writes log₂, and the proof of Prop. 8.8 (p.77) converts with ln 2 (log c ≥ (α−β)/(2αd ln 2), 14 ln 2 ≤ 10); the natural log would be a claim the paper does not make
--   - encoding: f^{⊗k} ⊆ Σ^k × Ω^k → prodRel R on prodDomain S k with outputs Fin k → Ω; reason: the same relation: s valid iff s_i ∈ f(x_i) for all i
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Theorem 9.8, p.87

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_Supplement_prodDomain

open scoped Matrix ENNReal

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

/-- **Theorem 9.8** (distributional direct product theorem; Ben-David, Ebtehaj, *Distributional
Quantum Query Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…, Theorem 9.8, p.87).
Let `Σ ⊆ {0,1}^n`, `f ⊆ Σ × Ω` a search problem, `μ` a distribution on `Σ`, success parameters
`0 < β < α < 1` and `k ≥ 1`. Then
`Q^{μ^{⊗k}}_{1−α^k}(f^{⊗k}) ≥ k(α − β)/(10α log(2(1−β)/(α−β))) · Q^μ_{1−β}(f)`.

**Formalization Note** `log = log₂` (`Real.logb 2`), the paper's convention (§2.3; the proof of
Proposition 8.8, p.77). The search problem is a total relation `R` (`∀ x, ∃ s, R x s`, §2.4,
p.17). `Q` is the base mission's `Qdist` (in `ℕ∞`), cast to `ℝ≥0∞`; the constant enters as
`ENNReal.ofReal`. `Σ^k` is `prodDomain S k` (positions `Fin k × ι`), `μ^{⊗k}` is `prodDist μ k`,
`f^{⊗k}` is `prodRel R` with outputs `Fin k → Ω`. -/
theorem theorem_9_8 {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s)
    (μ : S → ℝ) (hμ : IsDist μ) (α β : ℝ) (hβ0 : 0 < β) (hβα : β < α) (hα1 : α < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal ((k : ℝ) * (α - β) / (10 * α * Real.logb 2 (2 * (1 - β) / (α - β)))) *
        (Qdist S μ R (1 - β) : ℝ≥0∞) ≤
      (Qdist (prodDomain S k) (prodDist μ k) (prodRel R) (1 - α ^ k) : ℝ≥0∞) := by sorry

end DistQuantumQuery.Supplement
