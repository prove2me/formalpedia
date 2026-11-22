-- Prove2me | Theorems.Thm_CGWH_isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits
-- name    : CGWH.isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:26.699253+00:00
-- url     : https://prove2.me/theorems/bb1faf1a-1b17-499d-ab9e-553b3c7e90d9
-- title:
--   $\mathbf{CGWH}$ is a reflective subcategory of $\mathbf{CG}$, and it is complete and cocomplete
-- statement:
--   The category of compactly generated weakly Hausdorff spaces is reflective in the category of compactly generated spaces, and it has all small limits and all small colimits.
--
--   Let $\mathbf{CG}$ be the category of compactly generated topological spaces (spaces whose topology is determined by the continuous maps from compact Hausdorff spaces; no separation axiom) and continuous maps. A space $X$ is *weakly Hausdorff* if the image of every continuous map from a compact Hausdorff space to $X$ is closed in $X$. Let $\mathbf{CGWH}\subseteq\mathbf{CG}$ be the full subcategory of compactly generated weakly Hausdorff spaces and let
--   $$u_{\mathrm{wh}}:\mathbf{CGWH}\longrightarrow\mathbf{CG}$$
--   be the inclusion functor.
--
--   **Statement.**
--
--   1. The functor $u_{\mathrm{wh}}$ has a left adjoint $h:\mathbf{CG}\to\mathbf{CGWH}$ (the weak Hausdorffification).
--   2. $\mathbf{CGWH}$ has all small limits.
--   3. $\mathbf{CGWH}$ has all small colimits.
--
--   Since $u_{\mathrm{wh}}$ is a fully faithful right adjoint, limits in $\mathbf{CGWH}$ are computed in $\mathbf{CG}$ (as the $k$-ification of the limit of topological spaces), while the colimit of a diagram $P$ in $\mathbf{CGWH}$ is $h(\operatorname{colim}u_{\mathrm{wh}}\circ P)$, the weak Hausdorffification of the colimit formed in $\mathbf{CG}$; its underlying set can be a proper quotient of the colimit of the underlying sets. Together with cartesian closedness, this is what makes $\mathbf{CGWH}$ a convenient category of spaces; the paper develops its topological stacks over it.
--
--   **Formalization Note.** `CGWH.CGWHCat.{u}` and `CGWH.forgetToCG` come from the definition file `CGWH_WeakHausdorff`: the full subcategory of Mathlib's `CompactlyGenerated.{u, u}` on the weakly Hausdorff objects, and its inclusion functor. `Limits.HasLimits` and `Limits.HasColimits` refer to diagrams indexed by categories that are small with respect to the universe `u` of the spaces. The statement asserts the existence of a left adjoint (`Functor.IsRightAdjoint`) and does not name it; the explicit description $h(X)=X/R_X$ is the content of the companion theorem `CGWH.weakHausdorffification_universal`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 851-853, Lemma E.2.2.4(2) and Lemma E.2.2.5; classical reference (as cited by the paper for the left adjoint): N. Strickland, The category of CGWH spaces (available online), Prop. 2.22 and Cor. 2.23

import Definitions.Def_CGWH_WeakHausdorff

open CategoryTheory Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem isRightAdjoint_forgetToCG_and_hasLimits_and_hasColimits :
    (forgetToCG.{u}).IsRightAdjoint ∧ Limits.HasLimits CGWHCat.{u} ∧
      Limits.HasColimits CGWHCat.{u} := by sorry

end CGWH
