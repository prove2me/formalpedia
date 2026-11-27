-- Prove2me | Theorems.Thm_DeepSets_Supplement_lemma_4_powerSum_injOn
-- name    : DeepSets.Supplement.lemma_4_powerSum_injOn
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T04:26:14.924628+00:00
-- url     : https://prove2.me/theorems/9aedbc98-bcf5-498a-a5aa-e395ccbaa29a
-- title:
--   Lemma 4 — the sum-of-power mapping is injective on sorted tuples of $[0,1]^M$
-- statement:
--   Fix $M\ge 0$, let $\mathcal X=\{x\in[0,1]^M:x_1\le\cdots\le x_M\}$ and let $E:\mathcal X\to\mathbb R^{M+1}$ be the sum-of-power mapping $E_q(x)=\sum_{m=1}^M x_m^{\,q}$, $q=0,\dots,M$. Then $E$ is injective: for $u,v\in\mathcal X$,
--   $$
--   \sum_{m=1}^{M}u_m^{\,q}=\sum_{m=1}^{M}v_m^{\,q}\quad(q=0,\dots,M)\qquad\Longrightarrow\qquad u=v .
--   $$
--   Thus the first $M$ moments of $M$ numbers determine the numbers up to their order. The lemma is used in the proof of Theorem 7; it is not a step of the proof of Theorem 2. The sorting matters, since $E$ takes the same value on all the permutations of a tuple.
--
--   **Formalization Note** The statement is `Set.InjOn (powerSumMap M) (sortedUnitCube M)`.
--
--   Differences from the source:
--   - encoding: the mapping E : 𝒳 → ℝ^{M+1} → the map powerSumMap M on Fin M → ℝ, with injectivity asserted on sortedUnitCube M only (Set.InjOn); reason: Lean convention for a restricted map; same instances
--   - encoding: a fixed set size M, coordinates q = 0, …, M → any M : ℕ (M = 0 included), coordinates q : Fin (M + 1), with 0^0 = 1; reason: the page excludes no set size; at M = 0 both sides are single points
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.2, Lemma 4, eq. (8), p.12 (PDF p.12)

import Mathlib
import Definitions.Def_DeepSets_Supplement_sortedUnitCube
import Definitions.Def_DeepSets_Supplement_powerSumMap

namespace DeepSets.Supplement

/-- **Lemma 4** (Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.2, p.12). Let
`𝒳 = {(x₁, …, x_M) ∈ [0,1]^M : x₁ ≤ ⋯ ≤ x_M}`. The sum-of-power mapping `E : 𝒳 → ℝ^{M+1}`,
`E_q(x) = ∑_{m=1}^M (x_m)^q` for `q = 0, …, M`, is injective.

**Formalization Note** `E : 𝒳 → ℝ^{M+1}` is `powerSumMap M` on `sortedUnitCube M`, so injectivity
is `Set.InjOn`. The size `M` is any natural number. -/
theorem lemma_4_powerSum_injOn (M : ℕ) :
    Set.InjOn (powerSumMap M) (sortedUnitCube M) := by sorry

end DeepSets.Supplement
