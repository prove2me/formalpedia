-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_power_smul_restrict_of_isAffineOpen_of_isInvertible
-- name    : AlgebraicGeometry.Scheme.Modules.exists_power_smul_restrict_of_isAffineOpen_of_isInvertible
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T19:30:59.840056+00:00
-- url     : https://prove2.me/theorems/4dd949fe-c460-4a70-88d8-8e7652385ce9
-- title:
--   A power clears denominators of an invertible-sheaf section on a principal affine open
-- statement:
--   Let $X$ be a scheme, let $M$ be an invertible $\mathcal O_X$-module, let $U\subseteq X$ be an affine open subset, and let $f\in\Gamma(U,\mathcal O_X)$. Write $D_U(f)\subseteq U$ for the open locus where $f$ is invertible. Every section $s\in\Gamma(D_U(f),M)$ admits a power and an extension:
--
--   $$\exists n\in\mathbb N,\ \exists t\in\Gamma(U,M),\qquad
--   t|_{D_U(f)}=\bigl(f|_{D_U(f)}\bigr)^n s.$$
--
--   Thus multiplying a section on a principal open by a sufficiently large power of its defining function makes it the restriction of a section on the affine open. The exponent may depend on the section. This denominator-clearing property supplies common numerators in local constructions with sections of an invertible sheaf.
--
--   **Formalization Note.** The principal open is the actual nonvanishing locus of the section $f$. The conclusion uses the sheaf restriction maps and the action of its section ring. The function $f$ need not be a nonzerodivisor, and no regularity hypothesis on $X$ is imposed.
-- source:
--   Consequence of Stacks Project, Lemma 28.18.1, Tag 01P7 (https://stacks.math.columbia.edu/tag/01P7), applied to the affine scheme U and the restriction of the invertible sheaf M. The scheme U is quasi-compact and quasi-separated, and the restricted invertible sheaf is quasi-coherent. The lemma identifies Gamma(U,M)_f with Gamma(D_U(f),M). Write the given section as t/f^n and multiply by the invertible restriction of f^n. Only the surjectivity part of the localization statement is needed. There is no nonzerodivisor assumption and no uniqueness assertion.

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Opposite
universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_power_smul_restrict_of_isAffineOpen_of_isInvertible
    {X : Scheme.{u}} (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hU : IsAffineOpen U) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  sorry
