-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_theorem_1_4
-- name    : BourgainUnion.Euclidean.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:40.439671+00:00
-- url     : https://prove2.me/theorems/8fadaa9c-f2d2-493d-9d57-e148676bea1f
-- title:
--   Theorem 1.4 — two-sided distortion comparison
-- statement:
--   There is one constant $C\ge1$, valid for terminal combination as well, such that for every metric space $X$ covered by $k\ge1$ Euclidean subsets $U_i$, with $e_{\max}$ the maximal ambient Lipschitz extension constant after discarding empty members,
--   $$e_{\max}\le c_2(X)\le3\sqrt2\,C\,e_{\max}\log(k+1).$$
--   Both inequalities hold for arbitrary infinite and unbounded spaces. The lower bound is not dropped, and neither extension nor terminal hypotheses are added to the cover. This is the full comparison used to convert Lemma 1.5 into the goal's polynomial bound.
--
--   Differences from the source:
--   - encoding: real ℓ₂ and finite or infinite Euclidean target spaces → square-summable real sequences H2, with equivalent separable real Hilbert spaces where a dimension varies; reason: lp (fun _ : ℕ => ℝ) 2 is real ℓ₂; each separable real Hilbert space is isometric to a finite- or countably-dimensional ℓ₂ space
--   - encoding: a finite indexed cover that may overlap → U : Fin k → Set X and pointwise coverage; reason: zero-based indexing only; overlap and empty members are permitted unless nonemptiness is stated
--   - encoding: the least distortion or extension factor, potentially infinite → an infimum in ℝ≥0∞ of finite admissible factors at least one; reason: empty admissible sets give infinity; no real infimum default or unjustified attainment is used; empty and singleton spaces have the conventional factor one
--   - generalization: O(e_max log(k+1)) → 3√2 C e_max log(k+1), with the same universal terminal-combination constant C; reason: the factor from Lemma 3.1 is exposed; empty-space e_max is conventionally one, and the finite reduction of Appendix C is not a premise; the explicit form implies the source's asymptotic statement
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 3, Theorem 1.4 and §3

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Theorem 1.4 for arbitrary spaces; empty members are discarded by eMax. -/
theorem theorem_1_4 : ∃ C : ℝ, 1 ≤ C ∧ CombinationConstant C ∧
    ∀ (X : Type) [MetricSpace X] (k : ℕ), 1 ≤ k →
      ∀ U : Fin k → Set X, Covers U → (∀ i, IsEuclidean (U i)) →
        eMax U ≤ c2 X ∧
        c2 X ≤ ENNReal.ofReal (3*Real.sqrt 2*C*Real.log (k+1)) * eMax U := by sorry

end BourgainUnion.Euclidean
