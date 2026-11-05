-- Prove2me | Theorems.Thm_BrionAntiAffine_lemma_1_1
-- name    : BrionAntiAffine.lemma_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:39.401519+00:00
-- url     : https://prove2.me/theorems/7f38950d-6588-4f2d-b45e-da0d871349f9
-- title:
--   Lemma 1.1 — criteria for anti-affineness
-- statement:
--   Let $G$ be a group scheme of finite type over a field $k$. The following conditions are equivalent:
--
--   1. $G$ is anti-affine, i.e. $\mathcal O(G)=k$;
--   2. $G_K=G\otimes_k K$ is anti-affine for some field extension $K/k$;
--   3. every finite-dimensional linear representation of $G$ is trivial;
--   4. every action of $G$ on a variety $X$ containing a fixed point is trivial.
--
--   This parallels the characterization of affine group schemes by faithful representations, and reduces later statements to algebraically closed fields.
--
--   **Formalization Note** A representation is a matrix $\rho$ over $\Gamma(G,\mathcal O_G)$, quantified over all sizes. A fixed point is a closed point, by the conventions of p.3.
--
--   Differences from the source:
--   - encoding: a finite-dimensional linear representation of G → an invertible matrix over Γ(G, O_G) with μ^*ρ = pr₁^*ρ · pr₂^*ρ and η^*ρ = 1; trivial means ρ = 1; reason: a representation on kⁿ in a chosen basis is the same data
--   - encoding: some field extension K/k → K in the universe of k; reason: any witness forces (i), and then K = k is a witness
-- source:
--   M. Brion, Anti-affine algebraic groups, arXiv:0710.5211v3, Lemma 1.1, p.4

import Mathlib
import Definitions.Def_BrionAntiAffine_IsExactSeq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace BrionAntiAffine

variable {k : Type u} [Field k]

/-- Lemma 1.1, Brion, arXiv:0710.5211v3, p.4: criteria for anti-affineness. For a `k`-group scheme
`G` the following are equivalent: (i) `G` is anti-affine; (ii) `G_K` is anti-affine for some field
extension `K/k`; (iii) every finite-dimensional linear representation of `G` is trivial; (iv) every
action of `G` on a variety `X` containing a fixed point is trivial.

**Formalization Note.** `G` is of finite type, by the conventions of p.3. A representation is a matrix
(`IsMatrixRep`), so that (iii) quantifies over all `n`; in (ii) `K` is in the universe of `k`. -/
theorem lemma_1_1 (G : Sch k) [GrpObj G] (hG : IsFiniteTypeOver G) :
    List.TFAE
      [IsAntiAffine G,
       ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), IsAntiAffine (baseChange G K),
       ∀ (n : ℕ) (ρ : Matrix (Fin n) (Fin n) Γ(G.left, ⊤)), IsMatrixRep G n ρ → ρ = 1,
       ∀ (X : Sch k) (a : G ⊗ X ⟶ X), IsVariety X → IsLeftAction a →
         (∃ x : X.left, IsFixedPoint a x) → a = snd G X] := by sorry

end BrionAntiAffine
