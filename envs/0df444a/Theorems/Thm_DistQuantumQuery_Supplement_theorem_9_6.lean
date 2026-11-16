-- Prove2me | Theorems.Thm_DistQuantumQuery_Supplement_theorem_9_6
-- name    : DistQuantumQuery.Supplement.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:49:00.560201+00:00
-- url     : https://prove2.me/theorems/2cc08c1a-8dd2-4335-baf7-cc872673b917
-- title:
--   Theorem 9.6 — exact direct product: $\mathrm{AAdv}^{\mu^{\otimes k}}_{\alpha^k}(f^{\otimes k})=k\cdot\mathrm{AAdv}^\mu_\alpha(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, let $f\subseteq\Sigma\times\Omega$ be a search problem, let $\mu$ be a distribution on $\Sigma$, let $\alpha\in(0,1]$ and let $k\ge1$ be an integer. Then
--   $$
--   \mathrm{AAdv}^{\mu^{\otimes k}}_{\alpha^k}\big(f^{\otimes k}\big)=k\cdot\mathrm{AAdv}^\mu_\alpha(f),
--   $$
--   where $f^{\otimes k}\subseteq\Sigma^k\times\Omega^k$ is the $k$-fold problem, $\mu^{\otimes k}$ the product distribution, and the Alberti adversary measure on $\Sigma^k$ uses the sign filters of all $nk$ bit positions.
--
--   The Alberti adversary measure is exactly additive under independent repetition with multiplied success; this is the source of the direct-product theorem for query complexity (Theorem 9.8).
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: Σ^k ⊆ {0,1}^{nk}, x = (x_1,…,x_k), μ^{⊗k} → prodDomain S k ⊆ (Fin k × ι → Bool), block i read by blockOf, prodDist μ k = Π_j μ(x_j); reason: the same nk-bit strings queried bit by bit, with positions named (block, bit)
--   - encoding: f ⊆ Σ × Ω a search problem (a total relation, standing convention §2.4, p.17) → relation R : Σ → Ω → Prop with hypothesis ∀ x, ∃ s, R x s; reason: the paper's standing assumption stated once at the top of §2.4
--   - encoding: output set Ω → Ω a finite type; reason: measurements have a finite outcome set Ω (§2.3.2, p.16), as in the base Qdist
--   - encoding: f^{⊗k} ⊆ Σ^k × Ω^k → prodRel R on prodDomain S k with outputs Fin k → Ω; reason: the same relation: s valid iff s_i ∈ f(x_i) for all i
--   - encoding: AAdv as a min of δ̄₂ values in [0, +∞]; W/α; sign filters S_{ij} on Σ^k → AAdv in EReal as ⨅ over IsWitness; α⁻¹ • W; signFilters of the positions Fin k × ι; reason: same values (the minimum is attained, footnote 10); the sign filters of bit (i, j) are S_{ij} = J^{⊗(i−1)} ⊗ S_j ⊗ J^{⊗(k−i)}
--   - encoding: log in δ̄₂ (base 2) → Real.log; reason: the base cancels in the ratio −2 log F_c / log c
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Theorem 9.6, p.85

import Mathlib
import Definitions.Def_DistQuantumQuery_Supplement_prodDomain
import Definitions.Def_DistQuantumQuery_Supplement_AAdv

open scoped Matrix

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

/-- **Theorem 9.6** (exact direct product for the Alberti adversary; Ben-David, Ebtehaj,
*Distributional Quantum Query Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…,
Theorem 9.6, p.85). Let `Σ ⊆ {0,1}^n`, `f ⊆ Σ × Ω` a search problem, `μ` a distribution on `Σ`,
`α ∈ (0, 1]` and `k ≥ 1`. Then `AAdv^{μ^{⊗k}}_{α^k}(f^{⊗k}) = k · AAdv^μ_α(f)`.

**Formalization Note** The search problem is a total relation `R` (`∀ x, ∃ s, R x s`, the
paper's standing convention, §2.4, p.17). `Σ^k` is `prodDomain S k` (positions `Fin k × ι`, whose
sign filters are the `S_{ij}`), `μ^{⊗k}` is `prodDist μ k`, `f^{⊗k}` is `prodRel R` with outputs
`Fin k → Ω`. Both sides are in `EReal`; `k` is the natural number cast. -/
theorem theorem_9_6 {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Bool)) (R : S → Ω → Prop) (hR : ∀ x, ∃ s, R x s)
    (μ : S → ℝ) (hμ : IsDist μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    AAdv (prodDomain S k) (prodDist μ k) (prodRel R) (α ^ k) = (k : EReal) * AAdv S μ R α := by sorry

end DistQuantumQuery.Supplement
