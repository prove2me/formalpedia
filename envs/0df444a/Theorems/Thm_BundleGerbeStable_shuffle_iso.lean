-- Prove2me | Theorems.Thm_BundleGerbeStable_shuffle_iso
-- name    : BundleGerbeStable.shuffle_iso
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:45:58.71598+00:00
-- url     : https://prove2.me/theorems/951c6f69-7ab9-4f62-80ba-4e01e2a3000c
-- title:
--   Proof of Proposition 3.2: $P\otimes(Q^*\otimes Q)\cong Q\otimes(P\otimes Q^*)$
-- statement:
--   For bundle gerbes $(P,Y)$ and $(Q,Z)$ over a smooth manifold $M$, the bundle gerbes
--   $$P\otimes(Q^*\otimes Q)\quad\text{and}\quad Q\otimes(P\otimes Q^*)$$
--   over $Y\times_\pi(Z\times_\pi Z)$ and $Z\times_\pi(Y\times_\pi Z)$ are isomorphic, for every choice of the products.
--
--   This is the identity by which the proof of Proposition 3.2 derives stable isomorphism from the triviality of $P\otimes Q^*$.
--
--   Differences from the source:
--   - generalization: Y and P in a category of spaces "deduced from context": finite-dimensional manifolds, infinite-dimensional manifolds, differentiable spaces (p.2) → Y and P diffeological spaces in the universe of M, π smooth and locally split, with local triviality by diffeomorphisms; reason: the paper leaves the category open; diffeological spaces contain each named category, and a smooth map between manifolds is a diffeologically smooth one
--   - reading: "a manifold M" → M a finite-dimensional boundaryless smooth manifold of constant model E, Hausdorff and paracompact, with its manifold diffeology; no second countability, compactness or connectedness; reason: the paper's d(P) uses open covers with contractible intersections and H²(M, ℂ×) ≃ H³(M, ℤ) uses smooth partitions of unity; infinite-dimensional spaces occur in the paper as Y, not as this M
--   - encoding: contracted product P ⊗ Q with its fibres P_(y₁,y₂) ⊗ Q_(z₁,z₂) → a relation IsTensor G P Q, given by a smooth balanced multiplicative map t out of pairs (p, q); reason: the universal property of the contracted product; product_exists gives existence, and G is unique up to isomorphism
--   - reading: "P ⊗ (Q* ⊗ Q) = Q ⊗ (P ⊗ Q*)" → Nonempty (Iso G₁ G₂), for every choice of the products; reason: the two sides live over Y ×_π (Z ×_π Z) and Z ×_π (Y ×_π Z), which are different spaces
-- source:
--   Murray, Stevenson, Bundle gerbes: stable isomorphism and local theory, arXiv:math/9908135v1, https://arxiv.org/abs/math/9908135v1, proof of Proposition 3.2, p.4

import Mathlib
import Definitions.Def_BundleGerbeStable_Iso
import Definitions.Def_BundleGerbeStable_IsTensor

open Manifold ContDiff

namespace BundleGerbeStable

universe u

/-- **The isomorphism in the proof of Proposition 3.2** (Murray, Stevenson, *Bundle gerbes: stable isomorphism and local theory*, arXiv:math/9908135v1, p.4):
`P ⊗ (Q* ⊗ Q) = Q ⊗ (P ⊗ Q*)`.

**Formalization Note.** The two sides live over `Y ×_π (Z ×_π Z)` and `Z ×_π (Y ×_π Z)`, which are
different spaces, so "=" is read as `Nonempty (Iso …)`. It holds for every choice of the products. -/
theorem shuffle_iso (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [ParacompactSpace M] [DiffeologicalSpace M] [IsManifoldDiffeology E M]
    {S T : LocallySplit.{u} M} (P : BundleGerbe S) (Q : BundleGerbe T)
    (H₁ : BundleGerbe (fibreProd T T)) (G₁ : BundleGerbe (fibreProd S (fibreProd T T)))
    (H₂ : BundleGerbe (fibreProd S T)) (G₂ : BundleGerbe (fibreProd T (fibreProd S T)))
    (hH₁ : IsTensor H₁ Q.dual Q) (hG₁ : IsTensor G₁ P H₁)
    (hH₂ : IsTensor H₂ P Q.dual) (hG₂ : IsTensor G₂ Q H₂) :
    Nonempty (Iso G₁ G₂) := by sorry

end BundleGerbeStable
