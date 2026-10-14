-- Prove2me | Theorems.Thm_AlgebraicGeometry_CurveDegreeTests_exists_curve_degree_multisection
-- name    : AlgebraicGeometry.CurveDegreeTests.exists_curve_degree_multisection
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-13T16:20:17.60886+00:00
-- url     : https://prove2.me/theorems/9602745e-f756-4ac1-a058-990e0e145bc1
-- title:
--   Lifting curve tests through proper surjections with positive degree
-- statement:
--   Let $f:Y\to X$ be a proper surjective morphism of proper schemes over an algebraically closed field $K$. Let a curve test on $X$ be given by a smooth proper integral curve $C$ and $a:C\to X$, together with two affine charts covering $C$.
--
--   There are a smooth proper integral curve $D$, a map $b:D\to Y$, a finite surjective map $g:D\to C$, a two-affine-open cover of $D$, and a positive integer $d$, such that
--
--   $$f\circ b=a\circ g,\qquad
--   \deg_D(b^*f^*L)=d\,\deg_C(a^*L)$$
--
--   for every invertible sheaf $L$ on $X$. Here degrees are Euler characteristic differences on the specified covers. All choices, including $d>0$, precede the choice of $L$.
--
--   This normalized-curve multisection statement includes the degree identity needed to descend numerical triviality along proper surjections. It includes purely inseparable curve maps and does not assume $f$ is finite or flat. The multiplier $d$ is a positive integer even when the characteristic of $K$ divides it.
-- source:
--   Derived multisection consequence: choose a closed point of the generic fibre of Y times_X C and normalize its reduced closure. Stacks Project, Theorem 53.2.6 and Lemma 53.2.8 (https://stacks.math.columbia.edu/tag/0BXX) provide the normal projective curve and smoothness over a perfect field; Lemma 53.2.4 (https://stacks.math.columbia.edu/tag/0CCL) gives finiteness of the nonconstant map. The simultaneous degree identity is Lemma 33.44.11 (https://stacks.math.columbia.edu/tag/0AYZ), with degree defined by Definition 33.44.1. The charts are two affine opens on a smooth proper curve. This combines these standard facts rather than asserting a verbatim source theorem.

import Definitions.Def_AlgebraicGeometry_CurveDegreeTests
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.CurveDegreeTests.exists_curve_degree_multisection
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (f : Y ⟶ X) [IsProper f] [Surjective f] (t : CurveDegreeTests.Probe π) :
    ∃ (s : CurveDegreeTests.Probe (f ≫ π)) (g : s.curve ⟶ t.curve),
      IsFinite g ∧ Surjective g ∧ s.toScheme ≫ f = g ≫ t.toScheme ∧
        ∃ d : ℕ, 0 < d ∧ ∀ M : X.Modules, Scheme.Modules.IsInvertible M →
          s.degree ((Scheme.Modules.pullback f).obj M) = (d : ℤ) * t.degree M := by
  sorry
