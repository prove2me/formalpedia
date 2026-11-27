-- Prove2me | Theorems.Thm_DeepSets_Supplement_lemma_6_powerSum_continuous_inverse
-- name    : DeepSets.Supplement.lemma_6_powerSum_continuous_inverse
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:26:39.087327+00:00
-- url     : https://prove2.me/theorems/77492a6d-5bcd-5894-b101-05c3a6cce28b
-- title:
--   Lemma 6 — the sum-of-power mapping has a continuous inverse on its range
-- statement:
--   Fix $M\ge 0$, let $\mathcal X=\{x\in[0,1]^M:x_1\le\cdots\le x_M\}$, let $E_q(x)=\sum_{m=1}^M x_m^{\,q}$ for $q=0,\dots,M$, and let $\mathcal Z=E(\mathcal X)\subseteq\mathbb R^{M+1}$ be the range of $E$ on $\mathcal X$. Then $E:\mathcal X\to\mathcal Z$ has a continuous inverse: there is a continuous map $g:\mathcal Z\to\mathcal X$ with
--   $$
--   g(E(x))=x\quad(x\in\mathcal X),\qquad E(g(z))=z\quad(z\in\mathcal Z).
--   $$
--   So the sorted tuple depends continuously on its power sums. The lemma is used in the proof of Theorem 7, where it makes the outer function $\rho(z)=f(E^{-1}(z))$ continuous; it is not a step of the proof of Theorem 2.
--
--   **Formalization Note** $\mathcal X$ and $\mathcal Z$ carry the topologies induced by $\mathbb R^M$ and $\mathbb R^{M+1}$; $g$ is a map between the two subtypes.
--
--   Differences from the source:
--   - encoding: E : 𝒳 → 𝒵, where 𝒵 is the range of the function → powerSumMap M on sortedUnitCube M, with 𝒵 the image powerSumMap M applied to sortedUnitCube M, both sets with their subspace topologies; reason: Lean convention for a map onto its range; same instances
--   - encoding: "has a continuous inverse mapping" → there is a continuous g from 𝒵 to 𝒳 with both identities g(E(x)) = x and E(g(z)) = z; reason: this is the definition of a continuous inverse mapping
--   - encoding: a fixed set size M, coordinates q = 0, …, M → any M : ℕ (M = 0 included), coordinates q : Fin (M + 1), with 0^0 = 1; reason: the page excludes no set size; at M = 0 both sets are single points
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.2, Lemma 6, eq. (13), p.13 (PDF p.13)

import Mathlib
import Definitions.Def_DeepSets_Supplement_sortedUnitCube
import Definitions.Def_DeepSets_Supplement_powerSumMap

namespace DeepSets.Supplement

/-- **Lemma 6** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.2, p.13). Let
`𝒳 = {(x₁, …, x_M) ∈ [0,1]^M : x₁ ≤ ⋯ ≤ x_M}` and let `E : 𝒳 → 𝒵` be the sum-of-power mapping
`E_q(x) = ∑_{m=1}^M (x_m)^q`, `q = 0, …, M`, where `𝒵` is the range of the function. The function
`E` has a continuous inverse mapping.

**Formalization Note** `𝒵` is the image `powerSumMap M '' sortedUnitCube M`. The inverse is a map
`g : 𝒵 → 𝒳` between the two sets with their subspace topologies, and both identities
`g(E(x)) = x` on `𝒳` and `E(g(z)) = z` on `𝒵` are asserted. -/
theorem lemma_6_powerSum_continuous_inverse (M : ℕ) :
    ∃ g : ↥(powerSumMap M '' sortedUnitCube M) → ↥(sortedUnitCube M),
      Continuous g ∧
      (∀ x : ↥(sortedUnitCube M),
        g ⟨powerSumMap M x.1, Set.mem_image_of_mem (powerSumMap M) x.2⟩ = x) ∧
      (∀ z : ↥(powerSumMap M '' sortedUnitCube M), powerSumMap M (g z).1 = z.1) := by sorry

end DeepSets.Supplement
