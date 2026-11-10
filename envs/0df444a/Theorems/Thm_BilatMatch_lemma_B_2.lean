-- Prove2me | Theorems.Thm_BilatMatch_lemma_B_2
-- name    : BilatMatch.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:13:09.649402+00:00
-- url     : https://prove2.me/theorems/345adc92-ece6-41d1-9c51-15ab7139cf4a
-- title:
--   Lemma B.2 (Seller Reconstruction) — strictly increasing support, same atom probabilities, $\tau^\alpha_{\hat S}(\hat c_k)=\bar\tau^\alpha_S(c_k)$
-- statement:
--   Fix $\alpha\ge0$ and a finitely supported seller prior with atoms $c_1<\dots<c_m$. The reconstruction recursion $\hat C_k+\alpha F_S(c_k)\hat c_k=\Phi(F_S(c_k))$ gives a strictly increasing support $\hat c_1<\dots<\hat c_m$ with the original atom probabilities, $\hat F_S(\{\hat c_k\})=f_S(c_k)$, and its $\alpha$-virtual costs equal the original ironed costs:
--   $$\tau^\alpha_{\hat S}(\hat c_k)=\bar\tau^\alpha_S(c_k)\qquad(k=1,\dots,m).$$
--
--   **Formalization Note** Atoms are indexed from $0$. The statement also records that the atoms of $\hat F_S$ are exactly $\hat c_1,\dots,\hat c_m$.
--
--   Differences from the source:
--   - encoding: a strictly increasing support with the original atom probabilities → the ĉ_k are strictly increasing in k, F̂_S({ĉ_k}) = f_S(c_k), and the atoms of F̂_S are exactly the ĉ_k; reason: same content, spelled out
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.2, p.32 (pdf p.34); recursion p.31 (pdf p.33)

import Mathlib
import Definitions.Def_BilatMatch_reconLaw

open MeasureTheory

namespace BilatMatch

/-- **Lemma B.2 (Seller Reconstruction).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Lemma B.2, p.32 (pdf p.34); the recursion is on p.31 (pdf p.33).

For `α ≥ 0` and a finitely supported seller prior with atoms `c_1 < ⋯ < c_m`, the recursion
`Ĉ_k + α F_S(c_k) ĉ_k = Φ(F_S(c_k))`, `Ĉ_k = ∑_{h ≤ k} f_S(c_h) ĉ_h`, gives a strictly increasing
support `ĉ_1 < ⋯ < ĉ_m` with the original atom probabilities, and its `α`-virtual costs equal the
original ironed `α`-virtual costs: `τ^α_{Ŝ}(ĉ_k) = τ̄^α_S(c_k)`.

**Formalization Note** Atoms are indexed from `0` (`sortedAtom μ k`, `k < nAtoms μ`); `reconLaw α μ`
puts mass `f_S(c_k)` on `ĉ_k = reconCost α μ k`. -/
theorem lemma_B_2 (α : ℝ) (hα : 0 ≤ α) (μ : Measure ℝ) (hμ : IsFiniteSupport μ) :
    (∀ k k' : ℕ, k < k' → k' < nAtoms μ → reconCost α μ k < reconCost α μ k') ∧
    (∀ k < nAtoms μ, reconLaw α μ {reconCost α μ k} = μ {sortedAtom μ k}) ∧
    atoms (reconLaw α μ) = (fun k => reconCost α μ k) '' Set.Iio (nAtoms μ) ∧
    (∀ k < nAtoms μ, alphaVirtualCost α (reconLaw α μ) (reconCost α μ k) =
      ironedCost α μ (sortedAtom μ k)) := by sorry

end BilatMatch
