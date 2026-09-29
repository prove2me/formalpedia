-- Prove2me | Theorems.Thm_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
-- name    : CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/47dfc34f-2f05-51bb-a26b-e810c17c1093
-- title:
--   Primitive vectors parametrise double cosets Γ_H(M)backslashSL₂(ℤ)/⟨ g⟩
-- statement:
--   Let $M$ be a natural number, assumed nonzero, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $g \in \mathrm{SL}(2,\mathbb{Z})$. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}(2,\mathbb{Z})$, namely the image in $\mathrm{SL}(2,\mathbb{Z})$ of those $\gamma \in \Gamma_0(M)$ whose lower-right entry, reduced modulo $M$ (a unit, with inverse the reduction of the upper-left entry), lies in $H$. The assertion is that there exists a map $c$ from the subtype of those vectors $v : \mathrm{Fin}\,2 \to \mathbb{Z}/M$ with $\mathrm{addOrderOf}\,v = M$ to the double coset quotient of $\mathrm{SL}(2,\mathbb{Z})$ by the underlying sets of $\Gamma_H(M)$ on one side and of the subgroup $\langle g\rangle$ of integer powers of $g$ on the other, such that: (i) $c$ is surjective; and (ii) for all such $v, v'$, one has $c(v) = c(v')$ if and only if there are an integer $k$ and a unit $h \in H$ with $v' = h \cdot \big(\overline{g^{\,k}}\, v\big)$, where $\overline{g^{\,k}}$ denotes the entrywise reduction of $g^{k}$ modulo $M$ acting on $v$ by matrix–vector multiplication and $h$ acts by scalar multiplication on $(\mathbb{Z}/M)^2$.
--
--   This is the classical parametrisation of $\Gamma_H(M)\backslash\mathrm{SL}(2,\mathbb{Z})/\langle g\rangle$ by primitive vectors of $(\mathbb{Z}/M)^2$ — those of exact additive order $M$ — taken modulo the scalar action of $H$ and the action of the powers of $g$; the surjection $c$ together with the explicit fibre criterion is the form in which the bijection is packaged. It is used in the count of torsion orbits and double cosets for Weierstrass curves in characteristic two, via [`WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two`](thm.html#WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two), and rests on the surjectivity of reduction $\mathrm{SL}(2,\mathbb{Z}) \to \mathrm{SL}(2,\mathbb{Z}/M)$ recorded in [`ModularCurve.surjective_specialLinearGroup_map_zmod`](thm.html#ModularCurve.surjective_specialLinearGroup_map_zmod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ c : {v : Fin 2 → ZMod M // addOrderOf v = M} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers g : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ v v', c v = c v' ↔ ∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧
        v'.1 = (h : ZMod M) •
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g ^ k)).1.mulVec v.1) := by sorry
