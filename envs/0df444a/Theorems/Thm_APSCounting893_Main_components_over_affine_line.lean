-- Prove2me | Theorems.Thm_APSCounting893_Main_components_over_affine_line
-- name    : APSCounting893.Main.components_over_affine_line
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:40.074552+00:00
-- url     : https://prove2.me/theorems/b8106490-df69-4686-9d14-5927e8a050eb
-- title:
--   Lemma 3.9 — Components over an affine line
-- statement:
--   Let $K$ be any algebraically closed field and let $X$ be a nonempty irreducible affine variety of dimension $d\ge1$. Let $\pi:X\to K^d$ be finite and dominant. For any affine line $L=b+K\alpha$, with $\alpha\ne0$, and $C=\pi^{-1}(L)$, every irreducible component $W$ satisfies
--
--   $$\pi(W)=L.$$
--
--   Moreover, every point of every fiber above a point of $L$ belongs to such a component of $C$. Both clauses hold in every characteristic. Components, dominance and finiteness refer to the actual polynomial morphism.
--
--   Differences from the source:
--   - encoding: an arbitrary affine line and morphism of affine varieties → a base point and nonzero direction, and polynomial coordinate representatives for the morphism; reason: every affine line and every affine morphism admits this representation
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 3.9, p. 13, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Geometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem components_over_affine_line (K : Type) [Field K] [IsAlgClosed K] (a d : ℕ) (hd : 0 < d)
    (X : Set (Affine K a)) (hirr : IrreducibleAffine X)
    (hdim : RSCapacity.algDim X = ((d : ℕ∞) : WithBot ℕ∞))
    (pi : PolynomialMap K a d) (hfinite : FiniteMorphism X pi)
    (hdom : RSCapacity.zClosure (evaluate pi '' X) = Set.univ)
    (base direction : Affine K d) (hdir : direction ≠ 0) :
    let L := affineLine base direction
    let C := {x | x ∈ X ∧ evaluate pi x ∈ L}
    (∀ W, AffineComponent C W → evaluate pi '' W = L) ∧
      ∀ b ∈ L, ∀ x ∈ X, evaluate pi x = b →
        ∃ W, AffineComponent C W ∧ x ∈ W := by sorry

end APSCounting893.Main
