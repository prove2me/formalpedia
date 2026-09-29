-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_ideal_forall_map_eq_iff_le_ker
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_ideal_forall_map_eq_iff_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/c3154275-bc1b-5f69-8e50-74ea5191e3f0
-- title:
--   Coincidence of two Deligne data is cut out by an ideal
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $K$ a field equipped with an $\mathcal{O}$-algebra structure, $\pi$ an element of $\mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $d_1,d_2$ be two Deligne data over $B$ relative to $\pi$, that is, two assignments to each full lattice $M\subseteq K^2$ of a $B$-submodule $\mathrm{line}\,M$ of $B\otimes_{\mathcal{O}}M$ whose quotient is an invertible $B$-module, compatible with inclusions of lattices (the image of $\mathrm{line}\,M'$ in $B\otimes_{\mathcal{O}}M$ lies in $\mathrm{line}\,M$ when $M'\subseteq M$) and with the action of scalar homotheties $\mathrm{scalarGL}(c)$, $c\in K^{\times}$, and satisfying the nondegeneracy condition at every prime $\mathfrak{p}$ of $B$ recorded in the definition of `DeligneDatum`. The assertion is that there exists an ideal $I$ of $B$, depending only on $d_1$ and $d_2$, such that for every commutative $\mathcal{O}$-algebra $C$ and every $\mathcal{O}$-algebra homomorphism $\chi\colon B\to C$, the base-changed data $d_1.\mathrm{map}\,\pi\,\chi$ and $d_2.\mathrm{map}\,\pi\,\chi$ coincide — their lines at each $M$ being the $C$-span of the image of $\mathrm{line}\,M$ under $\chi\otimes\mathrm{id}_M$ — if and only if $I$ is contained in the kernel of $\chi$. Note that the ideal is produced uniformly in $C$ and $\chi$.
--
--   This says that, for the functor of Deligne data modelling Drinfeld's formal upper half plane by kernel lines, the locus in $\operatorname{Spec}B$ where two $B$-points agree is the closed subscheme cut out by a single ideal; no hypothesis of nilpotence of $\pi$ or finiteness is needed. It is used in the proof that the formal scheme $\Omega$ is separated, via [`CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints`](thm.html#CerednikDrinfeld.FormalOmega.Omega.isSeparated_of_equiv_nilpPoints), where the closedness of the image of the diagonal is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_ideal_forall_map_eq_iff_le_ker.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped TensorProduct

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_ideal_forall_map_eq_iff_le_ker
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d₁ d₂ : DeligneDatum (K := K) π B) :
    ∃ I : Ideal B, ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C),
      d₁.map π χ = d₂.map π χ ↔ I ≤ RingHom.ker (χ : B →+* C) := by sorry
