-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_b_2
-- name    : DimFreeShadow.lemma_b_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:34.119899+00:00
-- url     : https://prove2.me/theorems/60228083-863c-4cc2-abf0-470e69b789b6
-- title:
--   Lemma B.2 — CMI chain rule and the entropy bound for a classical label
-- statement:
--   Let $J$ be a classical register with at most $k$ possible values and $Q_1,\dots,Q_N$ finite-dimensional quantum registers. For every state on $J\otimes Q_1\otimes\dots\otimes Q_N$,
--
--   $$
--   \sum_{t=0}^{N-1}I(J:Q_{t+1}\mid Q_1\cdots Q_t)=I(J:Q_1\cdots Q_N)\le H(J)\le\log k,
--   $$
--
--   and every summand is nonnegative. Entropies are in natural logarithms.
--
--   The chain rule shows that on average over $t$ the next copy carries at most $\log k/N$ of information about the label, which drives the rate in Lemma 4.3.
--
--   Differences from the source:
--   - encoding: J classical with at most k possible values → ω block diagonal in the label index A, with card A ≤ k; reason: this is what a classical register means in matrix form
--   - encoding: registers Q_1, …, Q_N → index type (i : Fin N) → Q i, with t 0-based; reason: Lean convention; the registers may have different finite dimensions, as in the source
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma B.2, p.37

import Mathlib
import Definitions.Def_DimFreeShadow_labelEntropy
open scoped ComplexOrder

namespace DimFreeShadow

/-- **Lemma B.2** (arXiv:2608.06345, sha256 a1a42249…, Lemma B.2, p.37). If `J` is classical
with at most `k` possible values and `Q₁, …, Q_N` are finite-dimensional quantum registers,
then `Σ_{t=0}^{N−1} I(J : Q_{t+1} | Q₁⋯Q_t) = I(J : Q₁⋯Q_N) ≤ H(J) ≤ log k` (42), and every
summand is nonnegative.

**Formalization Note** The state `ω` (positive semidefinite, trace one) lives on
`J ⊗ Q₁ ⊗ ⋯ ⊗ Q_N`, indexed by `A × ((i : Fin N) → Q i)`; the registers may have different
finite dimensions. "`J` classical" is block diagonality in `J`: `⟨a, z| ω |a', z'⟩ = 0` for
`a ≠ a'`. "At most `k` values" is `|A| ≤ k`. Entropies are in nats (`P56.entropy`,
`Real.negMulLog`); `t` is 0-based. -/
theorem lemma_b_2 {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} {Q : Fin N → Type}
    [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
    (ω : Matrix (A × ((i : Fin N) → Q i)) (A × ((i : Fin N) → Q i)) ℂ)
    (hpsd : ω.PosSemidef) (htr : ω.trace = 1)
    (hcl : ∀ a a' : A, a ≠ a' → ∀ z z' : (i : Fin N) → Q i, ω (a, z) (a', z') = 0)
    (k : ℕ) (hk : Fintype.card A ≤ k) :
    ∑ t : Fin N, prefixCondMI ω t = labelMutualInfo ω ∧
    labelMutualInfo ω ≤ labelEntropy ω ∧
    labelEntropy ω ≤ Real.log k ∧
    ∀ t : Fin N, 0 ≤ prefixCondMI ω t := by sorry

end DimFreeShadow
