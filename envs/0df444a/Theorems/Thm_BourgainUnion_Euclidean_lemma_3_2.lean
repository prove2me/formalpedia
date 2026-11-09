-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_lemma_3_2
-- name    : BourgainUnion.Euclidean.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:44.512192+00:00
-- url     : https://prove2.me/theorems/ba4461e9-59ea-4d42-b531-2cf95a0c4a42
-- title:
--   Lemma 3.2 — distortion upper bound
-- statement:
--   There is one constant $C\ge1$, also valid for terminal combination in Theorem 2.7, such that the following holds. Let a finite metric space $X$ be covered by $k\ge1$ nonempty Euclidean subsets, and let $e_{\max}$ be the maximum of their ambient Lipschitz extension constants. Then
--   $$c_2(X)\le3\sqrt2\,C\,e_{\max}\log(k+1).$$
--   The comparison includes the constant from Lemma 3.1 explicitly and uses extended nonnegative values, without assuming that the optimal extension factor is attained. It is the finite-space upper-bound component of Theorem 1.4.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a finite indexed cover that may overlap → U : Fin k → Set X and pointwise coverage; reason: zero-based indexing only; overlap and empty members are permitted unless nonemptiness is stated
--   - encoding: the least distortion or extension factor, potentially infinite → an infimum in ℝ≥0∞ of finite admissible factors at least one; reason: empty admissible sets give infinity; no real infimum default or unjustified attainment is used; empty and singleton spaces have the conventional factor one
--   - generalization: O(e_max log(k+1)) → 3√2 C e_max log(k+1), with one C also satisfying CombinationConstant; reason: the proof composes exactly the factor from Lemma 3.1 and the universal constant from Theorem 2.7; the explicit form implies the source's asymptotic statement
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 11, Lemma 3.2

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Lemma 3.2 with the shared terminal-combination constant and factor from Lemma 3.1. -/
theorem lemma_3_2 : ∃ C : ℝ, 1 ≤ C ∧ CombinationConstant C ∧
    ∀ (X : Type) [MetricSpace X] [Fintype X] (k : ℕ), 1 ≤ k →
      ∀ U : Fin k → Set X, Covers U → (∀ i, (U i).Nonempty) →
        (∀ i, IsEuclidean (U i)) →
        c2 X ≤ ENNReal.ofReal (3*Real.sqrt 2*C*Real.log (k+1)) * eMax U := by sorry

end BourgainUnion.Euclidean
