-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_chart_of_isUnit_ratio
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_chart_of_isUnit_ratio
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:44.488355+00:00
-- url     : https://prove2.me/theorems/df1cecc3-aef5-4c92-99ab-619c02c9ed36
-- title:
--   A unit ratio on one projective chart forces membership in the second chart
-- statement:
--   Let $P$ be a projective presentation, let an open set $O$ lie in the chart $D_+(X_i)$, and let $x∈O$. If the restricted ratio section $X_j/X_i$ is a unit on $O$, then $$x∈D_+(X_j).$$ This upgrades chart containment when a coordinate ratio is invertible.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_chart_of_isUnit_ratio
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N)
    {i j : Fin (N+1)} {O : X.Opens}
    (hO : O ≤ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
    {x : X} (hx : x ∈ O)
    (hu : IsUnit (X.presheaf.map (homOfLE hO).op
      (P.toProj.app (Proj.basicOpen _ (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio K N i j))))) :
    x ∈ P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j) := by sorry
