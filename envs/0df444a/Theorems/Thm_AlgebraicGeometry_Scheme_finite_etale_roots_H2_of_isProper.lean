-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_etale_roots_H2_of_isProper
-- name    : AlgebraicGeometry.Scheme.finite_etale_roots_H2_of_isProper
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-18T19:13:48.289572+00:00
-- url     : https://prove2.me/theorems/9e728095-1d2d-44a5-8b71-5ce01d7bebe3
-- title:
--   Finiteness of second étale cohomology with roots of unity
-- statement:
--   Let $X$ be proper over an algebraically closed field, and let $n$ be a positive integer invertible on $X$. The group $$H^2_{\mathrm{et}}(X,\mu_n)$$ is finite, where $\mu_n$ is the étale sheaf of $n$-th roots of unity.
-- source:
--   SGA 4, Exposé XIV, Corollaire 1.2, https://grothendiecksga.com/read/sga4/en/XIV-1.html. The finite étale roots-of-unity sheaf is constructible by Stacks Project, Section 59.28, https://stacks.math.columbia.edu/tag/03PK.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SmallEtaleUnits

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.finite_etale_roots_H2_of_isProper
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ) (hn : n ≠ 0)
    (hu : IsUnit (n : Γ(X, ⊤))) : Finite ((PhilipponKummerSequence.roots X n).H 2) := by sorry
