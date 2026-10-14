-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_fibre_representatives_of_parameter_finiteType
-- name    : AlgebraicGeometry.RelPicard.exists_finite_fibre_representatives_of_parameter_finiteType
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T15:44:55.192832+00:00
-- url     : https://prove2.me/theorems/2e5dce47-9662-4a34-a5b7-1e205226774a
-- title:
--   Finitely many algebraic-equivalence classes in a finite-type line-bundle family
-- statement:
--   Let $K$ be an algebraically closed field, $X$ any $K$-scheme, and $T$ a finite-type $K$-scheme. Let $M$ be an invertible sheaf on $X\times_K T$.
--
--   There is a finite set $S\subset T(K)$ such that, for every $t\in T(K)$, some $r\in S$ and some invertible sheaf $N$ on $X$, algebraically equivalent to the trivial sheaf, satisfy
--
--   $$M_t\simeq N\otimes M_r.$$
--
--   The formal conclusion uses the existing base-change sheaves on $X\times_K\operatorname{Spec}K$ and the pullback of $N$ to that scheme. Algebraic equivalence is the existing concrete definition using an invertible sheaf on an integral parameter family with two marked rational fibres.
--
--   No properness or smoothness is assumed for $X$. The parameter scheme may be reducible or nonreduced. Finite type is expressed by locally finite type together with quasi-compactness. If there are no rational parameter points, the representative set may be empty.
--
--   This is the bounded-family finiteness step in a Néron–Severi argument. It does not assert that all numerically trivial invertible sheaves on a proper scheme belong to such a bounded family, or that the full Néron–Severi group is finitely generated.
-- source:
--   Elementary consequence of the parameter-family definition of algebraic equivalence and finite irreducible decomposition of a noetherian scheme. The proof uses Mathlib NoetherianSpace.exists_finset_irreducible, the universal property of reduced closed subschemes, and the existing Proved theorems AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal (66bd160f-a09e-531b-a8aa-79707f6f957b) and AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed (eca317a3-987b-54b5-a521-c23bef271d33). This supplies the elementary finite-family implication used with boundedness in SGA 6, Exposé XIII, Théorème 5.1, printed p. 650, https://library.slmath.org/nonmsri/sga/sga/pdf/sga6.pdf; it is not a literal transcription of that theorem.

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option autoImplicit false
open AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory CategoryTheory.Limits
open MonoidalCategory NeronModelInfra
universe u

theorem AlgebraicGeometry.RelPicard.exists_finite_fibre_representatives_of_parameter_finiteType
    (K : Type u) [Field K] [IsAlgClosed K] {X T : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) (h : T ⟶ Spec (.of K))
    [LocallyOfFiniteType h] [QuasiCompact h]
    (M : (pullback π h).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ s : Finset (SchemeHomOver (𝟙 (Spec (.of K))) h),
      ∀ t : SchemeHomOver (𝟙 (Spec (.of K))) h, ∃ r ∈ s,
        ∃ N : X.Modules, Scheme.Modules.IsInvertible N ∧ IsAlgEquivZero π N ∧
          Nonempty ((Scheme.Modules.pullback (baseChangeSnd π t)).obj M ≅
            (Scheme.Modules.pullback (pullback.fst π (𝟙 _))).obj N ⊗
              (Scheme.Modules.pullback (baseChangeSnd π r)).obj M) := by sorry
