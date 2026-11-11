-- Prove2me | Theorems.Thm_DistQuantumQuery_corollary_6_9
-- name    : DistQuantumQuery.corollary_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:37.656088+00:00
-- url     : https://prove2.me/theorems/f2ef8be8-9255-4f05-affb-5300b837ed4a
-- title:
--   Corollary 6.9 — $\Omega(\mathrm{rAdv}^\mu_{4\sqrt\varepsilon}(f))\le Q^\mu_\varepsilon(f)\le O(\mathrm{rAdv}^\mu_{\varepsilon/3}(f)/\varepsilon)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f:\Sigma\to\Omega$ functional, $\mu$ a distribution and $\varepsilon\in(0,1/2)$. Then for $\varepsilon\le1/16$,
--   $$
--   \Omega\big(\mathrm{rAdv}^\mu_{4\sqrt\varepsilon}(f)\big)\le Q^\mu_\varepsilon(f)\le O\!\left(\frac{\mathrm{rAdv}^\mu_{\varepsilon/3}(f)}{\varepsilon}\right).
--   $$
--   Moreover, if $f:\Sigma\to\{0,1\}$ is a decision problem, then for every $\varepsilon\in(0,1/2)$,
--   $$
--   \Omega\big(\mathrm{rAdv}^\mu_{2\sqrt{\varepsilon(1-\varepsilon)}}(f)\big)\le Q^\mu_\varepsilon(f)\le O\!\left(\frac{\mathrm{rAdv}^\mu_{\varepsilon/3}(f)}{\varepsilon}\right).
--   $$
--   The second statement of the main theorem rests on the upper bound.
--
--   **Formalization Note** The $\Omega(\cdot)$ and $O(\cdot)$ are absolute constants $c,C>0$, chosen before every instance and shared by both statements.
--
--   Differences from the source:
--   - encoding: Σ ⊂ {0,1}^n with positions [n] → Σ a Finset of bit strings ι → Bool over a finite type ι of positions; reason: relabelling positions; ι = Fin n is the source's case and every finite ι is a relabelling of some Fin n
--   - encoding: min / max / inf of measures, +∞ if unbounded; Q an integer → values in ℝ≥0∞ (Q in ℕ∞, cast to ℝ≥0∞); min/inf as ⨅, max/sup as ⨆; reason: same values, with ⊤ for +∞; no real cast that would send ⊤ to 0
--   - encoding: index register with basis |0⟩,…,|n⟩ and an arbitrarily large ancilla → work register Option ι × Fin (d+1), none the null index, d existential; reason: the same oracle model; Fin (d+1) always contains the start vector
--   - reading: projective measurement: Π_s² = Π_s, Π_sΠ_t = 0, Σ_r Π_r = I (§2.3.2) → each Π_s also Hermitian; reason: the same paragraph reads outcome probabilities as Tr[Π_s ρ], which requires orthogonal projectors
--   - encoding: constants uniform over all instances → instances quantified with index and output types in Type (universe 0); reason: every instance of the source has finite index and output sets, which live in Type up to relabelling
--   - encoding: “if f is a decision problem” (Ω = {0,1}) → a second clause for every g : Σ → Bool on the same Σ and μ; reason: Bool is {0,1}; the decision clause is stated for all decision problems on the same data
--   - reading: Ω(·), O(·) without subscripts → ∃ c, C > 0 chosen before Σ, μ, f, ε, one pair for both clauses; reason: the notation carries no dependence; the error may depend on n (p.22), so the constants are absolute; one pair for both clauses is the stronger reading (take min c and max C)
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Corollary 6.9, p.52

import Mathlib
import Definitions.Def_DistQuantumQuery_Qdist
import Definitions.Def_DistQuantumQuery_rAdv

open scoped Matrix ENNReal ComplexOrder Topology

namespace DistQuantumQuery

/-- **Corollary 6.9** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835,
held version, sha256 6334ffaf…, Corollary 6.9, p.52). Let `Σ ⊆ {0,1}^n`, `f : Σ → Ω` functional, `μ` a
distribution and `ε ∈ (0, 1/2)`. Then for `ε ≤ 1/16`,
`Ω(rAdv^μ_{4√ε}(f)) ≤ Q^μ_ε(f) ≤ O(rAdv^μ_{ε/3}(f)/ε)`.
Moreover, if `f : Σ → {0,1}` is a decision problem, then for every `ε ∈ (0, 1/2)`,
`Ω(rAdv^μ_{2√(ε(1−ε))}(f)) ≤ Q^μ_ε(f) ≤ O(rAdv^μ_{ε/3}(f)/ε)`.

**Formalization Note** The constants `c, C > 0` are absolute: chosen before the positions, `Σ`,
`μ`, the output set, `f` and `ε`, and shared by both clauses. Index and output types range over
`Type`. Values in `ℝ≥0∞`. -/
theorem corollary_6_9 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (S : Finset (ι → Bool)) (μ : S → ℝ), IsDist μ →
      (∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (f : S → Ω) (ε : ℝ), 0 < ε → ε < 1 / 2 →
        ε ≤ 1 / 16 →
        ENNReal.ofReal c * rAdv S μ f (4 * Real.sqrt ε) ≤ (Qdist S μ (graphRel f) ε : ℝ≥0∞) ∧
        (Qdist S μ (graphRel f) ε : ℝ≥0∞) ≤
          ENNReal.ofReal C * rAdv S μ f (ε / 3) / ENNReal.ofReal ε) ∧
      (∀ (g : S → Bool) (ε : ℝ), 0 < ε → ε < 1 / 2 →
        ENNReal.ofReal c * rAdv S μ g (2 * Real.sqrt (ε * (1 - ε))) ≤
          (Qdist S μ (graphRel g) ε : ℝ≥0∞) ∧
        (Qdist S μ (graphRel g) ε : ℝ≥0∞) ≤
          ENNReal.ofReal C * rAdv S μ g (ε / 3) / ENNReal.ofReal ε) := by sorry

end DistQuantumQuery
