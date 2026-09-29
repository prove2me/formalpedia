-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_hom_eq_id_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.iso_hom_eq_id_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/f42fa486-23b2-5ab5-9f72-5a723697acd6
-- title:
--   Rigidity of polarised abelian schemes with level n ≥ 3
-- statement:
--   Fix natural numbers $g, d, n$ with $3 \le n$, a commutative ring $S$ in which the image of $n$ is a unit, and $u$ a polarised abelian scheme of type $(g,d,n)$ over $S$: thus $u$ consists of a scheme $u.A$ with a structure morphism $u.f : u.A \to \operatorname{Spec} S$ that is smooth, proper and has connected fibres, a commutative relative group law $u.L$ on $T$-points of $u.f$ over $\operatorname{Spec} S$, the requirement that each fibre of $u.f$ have topological Krull dimension $g$, sections $u.P_i$ ($i < 2g$) of $u.f$ that are killed by $n$ and that, over every algebraically closed field receiving $S$, freely generate the $n$-torsion of the corresponding fibre, and an invertible module $u.\mathrm{pol}$ on $u.A$ which embeds $u.A$ as a closed subscheme of a relative projective space by its sections and has $H^0$ of rank $d$ on every geometric fibre. Let $e : u.A \cong u.A$ be an isomorphism of schemes such that $e.\mathrm{hom}$ followed by $u.f$ is $u.f$; such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x, y$ of $u.f$ over $t$, post-composition with $e.\mathrm{hom}$ carries $u.L.\mathrm{mul}\,t\,x\,y$ to the product of the post-composed points, i.e. $e$ is a homomorphism on points; such that each $u.P_i$ followed by $e.\mathrm{hom}$ equals $u.P_i$; and such that the polarisation is preserved locally on the base, in the sense that every point $p$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ for which the restrictions to $u.f^{-1}(U)$ of $(e.\mathrm{hom})^{*} u.\mathrm{pol}$ and of $u.\mathrm{pol}$ are isomorphic. Then $e.\mathrm{hom} = \mathrm{id}_{u.A}$.
--
--   This is the rigidity of the moduli problem of polarised abelian schemes with full level-$n$ structure for $n \ge 3$, in the form matching a fine moduli problem in which polarisations are compared only locally over the base: an automorphism fixing the level sections is trivial. It is obtained from the corresponding rigidity statement with a global identification of polarisation modules, [`AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le), together with the existence of base changes [`AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback), and is used in [`AlgebraicGeometry.FramedPolarisedAbelianScheme.eq_one_of_isReframe_inter_of_iso`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.eq_one_of_isReframe_inter_of_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_iso_hom_eq_id_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.iso_hom_eq_id_of_three_le
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    (u : PolarisedAbelianScheme g d n S) (e : u.A ≅ u.A) (he : e.hom ≫ u.f = u.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      (u.L.mul t x y).1 ≫ e.hom =
        (u.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1)
    (hP : ∀ i, (u.P i).1 ≫ e.hom = (u.P i).1)
    (hpol : ∀ p : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    e.hom = 𝟙 u.A := by sorry
