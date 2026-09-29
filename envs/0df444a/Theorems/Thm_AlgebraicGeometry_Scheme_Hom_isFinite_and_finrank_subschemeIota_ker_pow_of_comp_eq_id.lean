-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
-- name    : AlgebraicGeometry.Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/15e4eab7-8b2f-5c35-81d5-294a656195f8
-- title:
--   Powers of a section's ideal are finite flat of rank r
-- statement:
--   Let $X$ and $T$ be schemes and $p \colon X \to T$ a separated morphism which is smooth of relative dimension $1$. Let $\sigma \colon T \to X$ satisfy $\sigma$ followed by $p$ equal to $\mathrm{id}_T$, i.e. $\sigma$ is a section of $p$, and let $r$ be a natural number. Write $\sigma.\mathrm{ker}$ for the quasi-coherent ideal sheaf on $X$ that is the kernel of $\mathcal O_X \to \sigma_* \mathcal O_T$, form its $r$-th power in the semiring of quasi-coherent ideal sheaves (`Scheme.IdealSheafData`), and let $(\sigma.\mathrm{ker}^r).\mathrm{subscheme\iota}$ be the canonical closed immersion of the closed subscheme it cuts out into $X$. The assertion is a fourfold conjunction about the composite $q$ of this closed immersion with $p$: $q$ is a finite morphism; for every point $t$ of $T$ the rank `Scheme.Hom.finrank` of $q$ at $t$ equals $r$; $q$ is flat; and $q$ is locally of finite presentation. In other words, the $r$-th infinitesimal neighbourhood of the section $\sigma$ is finite, flat and locally of finite presentation over $T$, of constant rank $r$.
--
--   This is the statement that the divisor $r\cdot\sigma$ attached to a section of a smooth relative curve is a relative effective divisor of degree $r$: the subscheme $V(\mathcal I^{\,r})$ is finite locally free of rank $r$ over the base. It is the source of the degree-$r$ divisors used in the Euler-characteristic and Riemann–Roch computations on the relative Picard group, for instance in [`AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one`](thm.html#AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one) and the related counting results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
    {X T : Scheme.{u}} {p : X ⟶ T} [IsSeparated p] [SmoothOfRelativeDimension 1 p]
    (σ : T ⟶ X) (hσ : σ ≫ p = 𝟙 T) (r : ℕ) :
    IsFinite ((σ.ker ^ r).subschemeι ≫ p) ∧
      (∀ t : T, ((σ.ker ^ r).subschemeι ≫ p).finrank t = r) ∧
      Flat ((σ.ker ^ r).subschemeι ≫ p) ∧
      LocallyOfFinitePresentation ((σ.ker ^ r).subschemeι ≫ p) := by sorry
