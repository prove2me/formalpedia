-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_theorem_4_2
-- name    : BourgainUnion.Euclidean.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:09.583001+00:00
-- url     : https://prove2.me/theorems/0b82ee57-1a75-4853-8ff0-6faef307c271
-- title:
--   Theorem 4.2 — optimal sparsifier quality equals the squared extension constant
-- statement:
--   Let $X$ be a finite set, $U_1,\dots,U_k$ a partition of $X$ into nonempty sets, $\mathcal D$ the class of pseudometrics on $X$ that are Euclidean on every $U_j$, and $A=U_i$. Then the least Euclidean metric sparsifier quality $Q(\mathcal D,A)$ guaranteed for every weighted graph on $X$ and the uniform Lipschitz extension constant $e(\mathcal D,A)$ satisfy
--   $$Q(\mathcal D,A)=e(\mathcal D,A)^2 .$$
--   As a consequence, for every $k$, the suprema over all finite partitions into at most $k$ sets and all choices of $A$ satisfy
--   $$Q_k=e_k^2 .$$
--   Bounding Lipschitz extension constants thus reduces to constructing good sparsifiers.
--
--   Differences from the source:
--   - encoding: Q(D, A), e(D, A), Q_k, e_k → the same quantity in ℝ≥0∞ (⊤ when no finite constant exists); reason: infinite values are representable, so no finiteness is assumed and no real-infimum default 0 arises
--   - encoding: weighted graphs with g_xy = g_yx ≥ 0, g_xx = 0, and sums over unordered pairs x < y → the published ClusterDecomp.WGraph with the base Loopless predicate; energy = half the ordered-pair sum; reason: symmetry and the zero diagonal make the two sums equal
--   - encoding: a Euclidean pseudometric ρ on A → ρ : X → X → ℝ realized isometrically in ℓ2 on A (published RawEuclidean); values off A × A are ignored; reason: only the restriction of ρ to A enters (3) and (4)
--   - encoding: Lip(F) ≤ Λ·Lip(f) for every Lipschitz f : (A, d) → ℓ2 → for every L ≥ 0 and every L-Lipschitz f, an extension that is ΛL-Lipschitz for d; reason: the Lipschitz constant of a Lipschitz map is itself an admissible L
--   - encoding: suprema over all finite partitions into at most k sets and all A = U_i → suprema over finite types X : Type, partitions U : Fin j → Set X with j ≤ k, and i : Fin j; reason: every finite set is in bijection with a type in Type, and both quantities are invariant under relabeling
--   - encoding: a partition U1, …, Uk of X and A = U_i → the base Partition predicate and a Finset A with ↑A = U i; reason: the published definition of Section 4.1 partitions
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 14, §4.1, Theorem 4.2 (definitions pp. 13–14; proof Appendix A, pp. 30–31)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel
import Definitions.Def_BourgainUnion_Euclidean_Supplement_SparsifierModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Theorem 4.2, p. 14: `Q(D, A) = e(D, A)²` for every partition and every `A = U_i`, and
`Q_k = e_k²`; both in `ℝ≥0∞`, so no finiteness is assumed. -/
theorem theorem_4_2 :
    (∀ (X : Type) [Fintype X] (k : ℕ) (U : Fin k → Set X), Partition U →
      ∀ (i : Fin k) (A : Finset X), (A : Set X) = U i →
        sparsifierQuality U A = extensionConstantD U (U i) ^ 2) ∧
    (∀ k : ℕ, Qk k = ek k ^ 2) := by sorry

end BourgainUnion.Euclidean.Supplement
