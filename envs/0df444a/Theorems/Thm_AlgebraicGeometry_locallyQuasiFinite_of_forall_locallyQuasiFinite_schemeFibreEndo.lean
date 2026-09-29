-- Prove2me | Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
-- name    : AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/baa13755-481c-5893-9619-40fe9f026574
-- title:
--   Fibral criterion for local quasi-finiteness of an S-endomorphism
-- statement:
--   Let $S$ and $X$ be schemes in a fixed universe, let $f : X \to S$ be a morphism and let $h : X \to X$ be an endomorphism over $S$, in the sense that the hypothesis `hcomm` asserts $h$ followed by $f$ equals $f$ (i.e. $f \circ h = f$). For a point $s$ of $S$, `schemeFibreEndo f h hcomm s` is the endomorphism of the fibre product $X \times_S \operatorname{Spec} \kappa(s)$, formed along the canonical morphism $\operatorname{Spec} \kappa(s) \to S$ from the residue field at $s$, obtained by lifting the pair consisting of the first projection followed by $h$ and the second projection; the compatibility needed for the lift comes from `hcomm` together with the defining condition of the pullback. The hypothesis `hfib` is that for every point $s$ of $S$ this induced endomorphism of the fibre $X_s$ is locally quasi-finite in Mathlib's sense. The conclusion is that the morphism $h : X \to X$ itself is locally quasi-finite. No finiteness, noetherian or finite-type assumptions are imposed on $f$, $X$ or $S$.
--
--   This is the fibral criterion for local quasi-finiteness, in the special case of an endomorphism of $X$ over a base $S$: local quasi-finiteness of such an endomorphism may be checked on the fibres $X_s$. It is used in the study of the relative group law on Jacobians, where it supplies local quasi-finiteness of multiplication by $n$ on an abelian scheme from its behaviour on geometric fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
    {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (hfib : ∀ s : S, LocallyQuasiFinite (schemeFibreEndo f h hcomm s)) :
    LocallyQuasiFinite h := by sorry
