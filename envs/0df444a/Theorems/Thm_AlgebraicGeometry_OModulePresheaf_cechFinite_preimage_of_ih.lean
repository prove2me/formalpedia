-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih
-- name    : AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/82d81a0c-31a7-5917-9e34-126039abab0e
-- title:
--   Descent of the Čech-finiteness hypothesis to a closed subscheme
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme with a morphism $\pi\colon V\to\operatorname{Spec}R$, and $K$ an ordered affine cover of $V$, that is, a finite linearly ordered index set together with affine opens $U_i\subseteq V$ whose supremum is $\top$. Let $Z_0$ be a closed subset of $V$ and let $\iota$ denote the canonical closed immersion of the subscheme cut out by the vanishing ideal sheaf data of $Z_0$. Assume the induction hypothesis `ih`: for every closed subset $Y'$ of $V$ with $Y'<Z_0$ and every $G$ in `OModulePresheaf π` — a family of $R$- and $\Gamma(V,U)$-modules $G(U)$ indexed by the opens of $V$, with compatible scalar towers and $R$-linear restriction maps semilinear over restriction of functions and functorial — such that $G(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$ (`IsCoherent`), such that for every affine open $U$ and $f\in\Gamma(V,U)$ every section over the basic open $D(f)$ becomes the restriction of a section over $U$ after multiplication by a power of $f$ and every section over $U$ dying on $D(f)$ is killed by a power of $f$ (`IsQuasicoherent`), and such that $G(U)$ is a subsingleton whenever the affine open $U$ misses $Y'$ (`SupportedIn Y'`), the $R$-modules $H^0(K,G)$ and all the higher cohomologies $\mathrm{HSucc}(K,G,i)$ of the ordered Čech complex of $K$ are finite (`CechFinite K`). Let then $F$ be an object of `OModulePresheaf` for $\iota$ followed by $\pi$, coherent and quasi-coherent in the above sense, and supported in a closed subset $Y'$ of the subscheme with $Y'<\top$. The conclusion is that $F$ is Čech-finite for the cover $K.\mathrm{preimage}\ \iota$, whose index set is that of $K$ and whose affine opens are the $\iota^{-1}(U_i)$.
--
--   This is the induction step, in the Noetherian-style induction on the support used to prove finiteness of Čech cohomology over the base ring, which transports the hypothesis available on $V$ for strictly smaller closed subsets to the closed subscheme attached to $Z_0$. It is used in the proof of [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)
    {Z₀ : TopologicalSpace.Closeds V}
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → G.CechFinite K)
    (F : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (Y' : TopologicalSpace.Closeds (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) (hY' : Y' < ⊤)
    (hFs : F.SupportedIn Y') :
    F.CechFinite (K.preimage (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι) := by sorry
