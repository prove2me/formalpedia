-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
-- name    : AlgebraicGeometry.SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2db09ddf-274f-5ef6-a80e-3e9b8dc12b16
-- title:
--   m-torsion of a split torus is μ_m^t of degree m^t
-- statement:
--   Let $\kappa$ be a field and $t$ a natural number, let $X$ be a scheme with a morphism $f : X \to \operatorname{Spec}\kappa$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to X \mid \varphi \circ f = t\}$ of $X$-points over each $\kappa$-scheme $(T,t)$, given by multiplication, unit and inverse operations satisfying associativity, the two unit laws and left inversion, with multiplication natural in $(T,t)$. Assume given an isomorphism $e : \operatorname{Spec}\kappa[\mathbf Z^t] \xrightarrow{\sim} X$, where $\kappa[\mathbf Z^t]$ is the monoid algebra on $\mathrm{Fin}\,t \to \mathbf Z$, such that $e$ followed by $f$ is the structure morphism $\operatorname{Spec}$ of $\kappa \to \kappa[\mathbf Z^t]$, and such that for every $n \in \mathbf N$ the morphism $e$ followed by $L$'s $n$-th power map `L.schemeNsmul n` (the underlying morphism of the $n$-fold $L$-multiple of the identity point of $X$) equals $\operatorname{Spec}$ of the algebra map induced by multiplication by $n$ on $\mathbf Z^t$ followed by $e$. Let $m > 0$. Then: (i) the projection $L.\mathrm{schemeKer}\,m \to \operatorname{Spec}\kappa$, where $L.\mathrm{schemeKer}\,m$ is the fibre product of the $m$-th power map `L.schemeNsmul m` with the unit section $\operatorname{Spec}\kappa \to X$ of $L$, is a finite morphism; (ii) there is an isomorphism $L.\mathrm{schemeKer}\,m \cong \operatorname{Spec}\kappa[(\mathbf Z/m)^t]$ compatible with the two structure morphisms to $\operatorname{Spec}\kappa$; and (iii) for the $\kappa$-algebra structure on $\Gamma(L.\mathrm{schemeKer}\,m, \top)$ induced by that structure morphism, $\dim_\kappa \Gamma(L.\mathrm{schemeKer}\,m, \top) = m^t$.
--
--   This is the standard computation of the $m$-torsion of a split torus of rank $t$, in the form needed when the torus is presented abstractly as a scheme with a relative group law whose power maps are intertwined with those of $\operatorname{Spec}\kappa[\mathbf Z^t]$: the kernel is $\mu_m^t$, finite of degree $m^t$ over $\kappa$. It feeds the torsion and toric-rank estimates for the Néron objects attached to the Jacobians of the modular curves $X_0$ and $X_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SplitTorusMu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
    {κ : Type u} [Field κ] (t : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ f)
    (e : torusScheme κ t ≅ X) (hef : e.hom ≫ f = torusStr κ t)
    (hen : ∀ n : ℕ, e.hom ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom κ (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ e.hom)
    (m : ℕ) (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (∃ e' : L.schemeKer m ≅ muScheme κ t m, e'.hom ≫ muStr κ t m = L.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤
     Module.finrank κ Γ(L.schemeKer m, ⊤) = m ^ t) := by sorry
