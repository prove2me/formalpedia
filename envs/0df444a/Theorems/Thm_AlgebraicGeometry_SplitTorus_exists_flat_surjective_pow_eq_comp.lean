-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp
-- name    : AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/862fbfb9-5c1c-59b6-9b8d-fecb3bcc0a0e
-- title:
--   Fppf-local m-th roots of points of the split torus
-- statement:
--   Let $S$ be a commutative ring, let $t, m$ be natural numbers with $m > 0$, and write $R = S[\mathbf{Z}^t]$ for the group algebra `AddMonoidAlgebra S (Fin t → ℤ)`, so that the split torus over $S$ is $\mathbb{G}_m^t = \operatorname{Spec} R$ with structure morphism the map of spectra induced by the structural algebra map $S \to R$. Let $U$ be a scheme, $hU \colon U \to \operatorname{Spec} S$ a morphism, and $\tau \colon U \to \mathbb{G}_m^t$ a morphism with $\tau$ followed by the torus structure morphism equal to $hU$, i.e. a $U$-valued point of the torus over $S$. The assertion is that there exist a scheme $U'$ and a morphism $c \colon U' \to U$ which is flat, surjective and locally of finite presentation (an fppf cover), together with a morphism $\sigma \colon U' \to \mathbb{G}_m^t$ such that $\sigma$ followed by the torus structure morphism equals $c$ followed by $hU$, and $\sigma$ followed by the morphism of spectra induced by the ring homomorphism $R \to R$ extending multiplication by $m$ on the character lattice (`AddMonoidAlgebra.mapDomainRingHom S (m • AddMonoidHom.id (Fin t → ℤ))`, i.e. the $m$-th power map $[m]$ of the torus) equals $c$ followed by $\tau$. No assumption that $m$ is invertible on $S$ is made.
--
--   This is the Kummer covering statement for the split torus: every $U$-valued point of $\mathbb{G}_m^t$ becomes an $m$-th power after an fppf base change, the cover being obtained by extracting $m$-th roots of the relevant units. It is used in the construction of fppf-local sections of the $m$-torsion subscheme of Néron models attached to the modular curves $X_H$ and $X_0$, in [`ModularCurve.JHNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre`](thm.html#ModularCurve.JHNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre) and [`ModularCurve.JZeroNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre`](thm.html#ModularCurve.JZeroNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp
    {S : Type u} [CommRing S] (t m : ℕ) (hm : 0 < m)
    {U : Scheme.{u}} (hU : U ⟶ Spec (CommRingCat.of S)) (τ : U ⟶ SplitTorus.torusScheme S t)
    (hτ : τ ≫ SplitTorus.torusStr S t = hU) :
    ∃ (U' : Scheme.{u}) (c : U' ⟶ U) (_ : Flat c) (_ : Surjective c) (_ : LocallyOfFinitePresentation c)
      (σ : U' ⟶ SplitTorus.torusScheme S t),
      σ ≫ SplitTorus.torusStr S t = c ≫ hU ∧
      σ ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (m • AddMonoidHom.id (Fin t → ℤ)))) = c ≫ τ := by sorry
