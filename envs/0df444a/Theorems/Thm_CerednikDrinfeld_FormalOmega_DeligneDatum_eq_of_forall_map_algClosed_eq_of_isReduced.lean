-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced
-- name    : CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_algClosed_eq_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/c4f3dd63-0712-500b-958e-f5046ff7d990
-- title:
--   Deligne data over a reduced ring are determined geometrically
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi$ an element of $\mathcal O$, and $B$ a reduced commutative $\mathcal O$-algebra. Let $d,d'$ be two Deligne data over $B$ with parameter $\pi$, that is, two assignments to every full lattice $M \subseteq K^2$ of a $B$-submodule $\mathrm{line}(M)$ of $B \otimes_{\mathcal O} M$ whose quotient $(B\otimes_{\mathcal O}M)/\mathrm{line}(M)$ is an invertible $B$-module, compatible with inclusions of lattices (the image of $\mathrm{line}(M')$ under the base-changed inclusion lies in $\mathrm{line}(M)$ when $M' \le M$), equivariant for the scalar matrices $c\cdot 1$, $c \in K^{\times}$, and satisfying the nondegeneracy condition at every prime $\mathfrak p$ of $B$ requiring a pair $M' \le M$ with $\pi M \subseteq M'$ such that the classes $1 \otimes v$ of vectors $v \in M \setminus M'$, respectively of vectors $v' \in M'$ not divisible by $\pi$ in $M$, avoid $\mathrm{line}(M) + \mathfrak p\cdot(B\otimes_{\mathcal O}M)$, respectively $\mathrm{line}(M') + \mathfrak p\cdot(B\otimes_{\mathcal O}M')$. Assume that for every algebraically closed field $\Omega$ in `Type` carrying an $\mathcal O$-algebra structure and every $\mathcal O$-algebra homomorphism $f : B \to \Omega$, the base changes of $d$ and $d'$ along $f$ agree, where the base change replaces each $\mathrm{line}(M)$ by the $\Omega$-span of its image under $f \otimes \mathrm{id}_M$. Then $d = d'$.
--
--   This is the statement that a point of Drinfeld's formal upper half plane, in the lattice-line (Deligne datum) description, over a reduced base is determined by its geometric points; reducedness is essential, since first-order deformations are invisible at algebraically closed fields. It is used in the rigidified special formal module theory, for the uniqueness of quadruples with prescribed lines and for the corresponding existence statement in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_algClosed_eq_of_isReduced
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsReduced B]
    (d d' : DeligneDatum (K := K) π B)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra 𝒪 Ω] (f : B →ₐ[𝒪] Ω),
      DeligneDatum.map (K := K) π f d = DeligneDatum.map (K := K) π f d') :
    d = d' := by sorry
