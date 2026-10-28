-- Prove2me | Theorems.Thm_AlgebraicGeometry_hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
-- name    : AlgebraicGeometry.hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T21:41:43.186381+00:00
-- url     : https://prove2.me/theorems/ae594a3b-8d61-41b8-8e72-b6a40e8b9e2f
-- title:
--   Generic curve fibrations admit dominating smooth covering families over a normal projective base model
-- statement:
--   Let $k$ be a field, let $S$ be an integral proper projective $k$-scheme with a specified projective embedding, and let $q:X\to S$ be a proper dominant morphism with $X$ integral. Fix the actual generic point $\eta$ of $S$, and assume
--   $$\dim X_\eta\leq1.$$
--
--   There is a finite intermediate extension $E/\kappa(\eta)$ inside the prescribed algebraic closure of $\kappa(\eta)$, a normal integral projective $k$-scheme $N$, and a proper surjective map $q_N:N\to S$ with
--   $$\dim N=\dim S.$$
--   A dense normal affine chart $\operatorname{Spec}B\hookrightarrow N$ is retained, where $B$ is an actual finitely generated $k$-subalgebra of $E$ with fraction field $E$. Its generic spectrum map is exactly the one induced by $E/\kappa(\eta)$, and the projective embedding of $N$ is compatible with its map to $S$.
--
--   On a dense open $U\subset N$ there is a smooth proper family $p_Y:Y\to U$ with an exhibited projective ambient model and an actual proper surjective covering map
--   $$h:Y\longrightarrow Z=X\times_S U.$$
--   The target family $Z\to U$ is flat and proper, and the composite $Y\to X$ is dominant. The projective ambient model is a closed subscheme of projective space over a principal localization of $B$, and its base change to $U$ is exactly $Y$.
--
--   The actual generic source is retained: there is a smooth projective $E$-scheme $C_0$ of dimension at most one with a proper surjection $a_0:C_0\to X_\eta$ over the finite field extension. The map $\operatorname{Spec}E\to N$ factors through $U$, and $C_0\to Y$ is cartesian over it. Its composite with $Y\to X$ is exactly $a_0$ followed by the original generic-fibre inclusion.
--
--   The theorem works in arbitrary universes and characteristic and does not assume normality of $X$ or algebraic closedness of $k$. It provides the finite-base and smooth-family preparation for the curve-fibration alteration argument. It asserts relative smoothness over the dense base open; semistable compactification and a global smooth projective alteration remain separate.
-- source:
--   Finite-base and family preparation for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Uses the accepted normal projective finite-generic-field base model https://prove2.me/theorems/a2fa0ad5-6962-47c5-9e21-5fc176c6d9cb , actual scalar-extended curve cover https://prove2.me/theorems/a0fdd6ed-d4f7-42ef-8b17-f8add5de7610 , and projective generic-cover family construction https://prove2.me/theorems/9d194c42-8928-4185-90b1-2e9ba53665ea . Exact iterated pullback comparisons preserve the original generic covering map, and density of the actual generic fibre proves dominance of the resulting map to X. This is the preparation stage; semistable compactification, base alteration and global regularization are not supplied.

import Definitions.Def_PhilipponMultiplicity_GenericCurveCoverFamily
import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.hasNormalProjectiveBaseSmoothCurveCoverFamily_of_dimension_le_one_genericFiber
    (k : Type u) [Field k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (π : S ⟶ Spec (.of k)) [IsProper π]
    (m : ℕ) (i : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π k m = π)
    (q : X ⟶ S) [IsProper q] [IsDominant q]
    (η : S) (hη : IsGenericPoint η Set.univ) (hdim : topologicalKrullDim (q.fiber η) ≤ 1) :
    AlgebraicGeometry.HasNormalProjectiveBaseSmoothCurveCoverFamily k π q η := by sorry
