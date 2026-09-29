-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint
-- name    : AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_singleton_genericPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/5bd9f4f1-f0dd-5571-bb35-b54fe72ab309
-- title:
--   Kernel of a quasi-compact morphism from an integral scheme
-- statement:
--   Let $C$ and $Y$ be schemes (in a fixed universe), let $f \colon C \to Y$ be a morphism of schemes, assume $C$ is integral, and assume $f$ is quasi-compact. Write $\eta_C$ for the generic point of $C$, which exists because the underlying space of $C$ is irreducible, and let $f(\eta_C)$ be its image under the continuous map underlying $f$. The assertion is an equality of quasi-coherent ideal sheaf data on $Y$: the kernel ideal sheaf `f.ker` of $f$, whose value on an affine open $U \subseteq Y$ is the kernel of the ring map $\Gamma(Y, U) \to \Gamma(C, f^{-1}U)$ induced by $f$, coincides with the vanishing ideal sheaf `Scheme.IdealSheafData.vanishingIdeal` of the closed subset $\overline{\{f(\eta_C)\}}$ of $Y$ (packaged with the proof that a closure is closed), i.e. with the radical ideal sheaf cutting out the reduced induced closed subscheme structure on that closure. Thus the scheme-theoretic image of $f$ is the reduced closed subscheme supported on the closure of the image of the generic point.
--
--   This is the standard description of the scheme-theoretic image of a quasi-compact morphism out of an integral scheme: it is reduced and supported on the closure of the image of the generic point. It is used in the analysis of the vertical components of a regular model, where each component of a special fibre is recovered as the vanishing ideal of the closure of its generic point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_singleton_genericPoint
    {C Y : Scheme.{u}} (f : C ⟶ Y) [IsIntegral C] [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨closure ({f.base (genericPoint C)} : Set Y), isClosed_closure⟩ := by sorry
