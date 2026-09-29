-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
-- name    : AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e57037ff-29b2-5ef7-958d-029285470287
-- title:
--   Restriction along σ is the action of σ⁻¹
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $F$, let $h\sigma$ witness that the underlying ring homomorphism of $\sigma$ is integral (a hypothesis required by the signature of restriction along a morphism, and automatic for an automorphism), and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$ under the structure map, distinct from $F$ itself, and whose underlying ring is a principal ideal ring. Restriction of $v$ along $\sigma$ is formed by regarding $F$ as an algebra over itself through $\sigma$ and pulling $v$ back, so that its valuation subring is the preimage $\{x \in F : \sigma x \in \mathcal{O}_v\}$. On the other side, $\mathrm{SemilinearAut}\,K\,F$ is the subgroup of pairs $(\tau_F, \tau_K) \in \mathrm{RingAut}\,F \times \mathrm{RingAut}\,K$ compatible with the structure map, $\mathrm{ofAlgAut}$ sends a $K$-algebra automorphism to the pair consisting of its underlying ring automorphism and the identity of $K$, and such an element acts on places by the pointwise image of the valuation subring under the first component. The assertion is that these two places coincide: restricting $v$ along $\sigma$ equals $\mathrm{ofAlgAut}(\sigma^{-1}) \cdot v$, whose valuation subring is $\sigma^{-1}(\mathcal{O}_v)$.
--
--   This is the dictionary lemma identifying the two ways an automorphism moves places of $F/K$: pull-back (restriction along $\sigma$, defined for any integral $K$-algebra map) and the push-forward action of the semilinear automorphism group, the two differing by inversion. It is the place-level counterpart of the corresponding statement for divisors, and is used to convert statements about places of translates of integral models under automorphisms into the $\mathrm{ofAlgAut}$ form, as in the results on Drinfeld curves and on models of modular curves that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by sorry
