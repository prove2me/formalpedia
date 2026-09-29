-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/fff30be3-aa7d-5050-a7ce-9e3e3db95e98
-- title:
--   Geometric fibres of an affine invariant quotient are G-orbits
-- statement:
--   Let $M$ and $X$ be schemes, let $G$ be a finite group and let $\rho : G \to \operatorname{Aut}(M)$ be a group homomorphism into the automorphism group of $M$ in the category of schemes. Let $\pi : M \to X$ be a morphism such that (i) for every $g \in G$ the composite of $\rho(g)$ followed by $\pi$ equals $\pi$; (ii) $\pi$ is an affine morphism; (iii) for every open $V \subseteq X$ the pull-back $\pi^{\ast} : \Gamma(X,V) \to \Gamma(M,\pi^{-1}V)$ is injective; and (iv) for every open $V \subseteq X$ the image of that pull-back consists exactly of those $s \in \Gamma(M,\pi^{-1}V)$ with $\rho(g)^{\ast} s = s$ for all $g \in G$, where $\rho(g)^{\ast}$ is the map on sections over $\pi^{-1}V$ induced by $\rho(g)$ (legitimate because $\rho(g)^{-1}(\pi^{-1}V) = \pi^{-1}V$ by (i)). Let $k$ be an algebraically closed field and let $x, x' : \operatorname{Spec} k \to M$ be two $k$-points with $x$ followed by $\pi$ equal to $x'$ followed by $\pi$. Then there exists $g \in G$ with $x' = x$ followed by $\rho(g)$.
--
--   This is the geometric-point form of the statement that the fibres of an affine quotient map by a finite group are exactly the $G$-orbits: hypotheses (iii) and (iv) say that $\mathcal O_X \to (\pi_*\mathcal O_M)^G$ is an isomorphism, so locally $A = B^G$. It is used in the Čerednik–Drinfeld part of the development to pass from a fine moduli scheme for quaternionic data to a coarse one, namely in [`CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient), [`CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff) and [`CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuli_of_quotient_of_isIndefiniteRamifiedExactlyAt`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuli_of_quotient_of_isIndefiniteRamifiedExactlyAt), where it yields injectivity of the coarse moduli map on geometric points up to the group action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_eq_comp_autHom_of_comp_eq_of_isAlgClosed
    {M X : Scheme.{0}} {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (π : M ⟶ X) (hπ : ∀ g : G, (ρ g).hom ≫ π = π) (haff : IsAffineHom π)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (k : Type) [Field k] [IsAlgClosed k] (x x' : Spec (CommRingCat.of k) ⟶ M) (h : x ≫ π = x' ≫ π) :
    ∃ g : G, x' = x ≫ (ρ g).hom := by sorry
