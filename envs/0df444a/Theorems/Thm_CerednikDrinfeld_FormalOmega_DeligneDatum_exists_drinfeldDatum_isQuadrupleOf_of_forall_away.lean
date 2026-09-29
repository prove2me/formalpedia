-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/3cd4e3d0-036f-51f4-81e5-1e0ee97d30e8
-- title:
--   Drinfeld data glue along a finite cover of Spec B
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with fraction field $K$ (an $\mathcal O$-algebra which is a fraction ring of $\mathcal O$), let $\pi\in\mathcal O$ be irreducible, and let $B$ be an $\mathcal O$-algebra in which the image of $\pi$ is nilpotent. Let $d$ be a Deligne datum over $B$ for $\pi$: an assignment, to each full $\mathcal O$-lattice $M\subset K^2$, of a $B$-submodule $\mathrm{line}(M)\subseteq B\otimes_{\mathcal O}M$ with invertible quotient, monotone for inclusions of lattices, equivariant for scalar homotheties, and satisfying the edge-nondegeneracy condition at every prime of $B$. Let $f_0,\dots,f_{k-1}\in B$ generate the unit ideal, and suppose given, for each $i$, a Drinfeld datum $Q_i$ over the localisation $B[1/f_i]$ (a pair of lattice families $N_0\le N_1$ on the spectrum with $\pi N_1\subseteq N_0$ and open membership conditions, two invertible modules $T_0,T_1$ linked by maps composing to multiplication by $\pi$, together with stalkwise comparison maps $u_0,u_1$) which is a quadruple of the base change of $d$ along $B\to B[1/f_i]$, i.e. at every prime the edge-nondegeneracy holds for the lattices of $Q_i$ and the kernels of $u_0,u_1$ are the lines attached by the localised Deligne datum. Then there exists a Drinfeld datum $Q$ over $B$ which is a quadruple of $d$ in the same sense.
--
--   This is the gluing step in the construction of the Drinfeld quadruple attached to a Deligne datum over a base in which $\pi$ is nilpotent: local solutions over a finite cover of $\operatorname{Spec} B$ by basic open sets patch to a global one. It feeds the unconditional existence statement [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_forall_away.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf_of_forall_away
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B)
    {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hQ : ∀ i : Fin k, (Q i).IsQuadrupleOf
      (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    ∃ Qg : DrinfeldDatum (K := K) π B, Qg.IsQuadrupleOf d := by sorry
