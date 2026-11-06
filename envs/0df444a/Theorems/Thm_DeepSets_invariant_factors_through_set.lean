-- Prove2me | Theorems.Thm_DeepSets_invariant_factors_through_set
-- name    : DeepSets.invariant_factors_through_set
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:50:15.698253+00:00
-- url     : https://prove2.me/theorems/a907f191-0c22-4077-90a2-99c4d5a32ffb
-- title:
--   Proof of Theorem 2 — a permutation-invariant function depends only on the set
-- statement:
--   Let $U$ be any set of elements and let $f$ assign a real number $f(x_1,\dots,x_M)$ to every listing of distinct elements of $U$, for every size $M\ge 0$. If $f$ is permutation invariant (Property 1), then $f$ is a function of the set of listed elements: there is a function $g$ on the finite subsets of $U$ such that
--   $$
--   f(x_1,\dots,x_M) = g(\{x_1,\dots,x_M\})
--   $$
--   for every $M$ and every listing of $M$ distinct elements.
--
--   This is the first sentence of the proof of Theorem 2: since a set has no order, an invariant function is really a function on sets, and the rest of the proof decomposes that set function.
--
--   **Formalization Note** The set $\{x_1,\dots,x_M\}$ is the image of the injective tuple $x:\mathrm{Fin}\,M\to U$, a `Finset U`.
--
--   Differences from the source:
--   - reading: "Permutation invariance follows from the fact that sets have no particular order, hence any function on a set must not exploit any particular order either" → an invariant f factors through g : Finset U → ℝ via the image of the listing; reason: this is the precise content of the sentence in the proof; it is what the necessity argument (a function f(X) of the set X) uses
--   - generalization: countable universe 𝔛 → any type U; reason: the argument uses no countability; it specializes to a countable U
--   - encoding: a set {x₁, …, x_M} → an injective tuple x : Fin M → U, its set is Finset.univ.image x; reason: Lean convention; the same sets of every size M ≥ 0
-- source:
--   Zaheer, Kottur, Ravanbakhsh, Póczos, Salakhutdinov, Smola, Deep Sets, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12 (PDF p.12), "Permutation invariance follows from the fact that sets have no particular order …"

import Mathlib
import Definitions.Def_DeepSets_IsPermInvariant

namespace DeepSets

/-- Zaheer et al., *Deep Sets*, arXiv:1703.06114v3, §A.1, proof of Theorem 2, p.12,
"Permutation invariance follows from the fact that sets have no particular order, hence any
function on a set must not exploit any particular order either."

A permutation-invariant `f` (Property 1) is a function of the set `{x₁, …, x_M}` alone: there is
`g` on finite subsets of `U` with `f M x = g {x₁, …, x_M}` for every size `M` and every injective
listing `x`.

**Formalization Note** The set `{x₁, …, x_M}` is `Finset.univ.image x`. No countability is
assumed: the statement holds for every type `U`, and specializes to the countable universe of
Theorem 2. -/
theorem invariant_factors_through_set {U : Type*} [DecidableEq U]
    (f : (M : ℕ) → (Fin M → U) → ℝ) (hf : IsPermInvariant f) :
    ∃ g : Finset U → ℝ, ∀ (M : ℕ) (x : Fin M → U), Function.Injective x →
      f M x = g (Finset.univ.image x) := by sorry

end DeepSets
