-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_Iso_subsingleton
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.Iso.subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/62efb315-29b7-59b9-a15e-38240abee6bf
-- title:
--   Uniqueness of isomorphisms between Drinfeld data
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field equipped with an $\mathcal O$-algebra structure, $\pi$ an element of $\mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $Q$ and $Q'$ be two Drinfeld data for $\pi$ over $B$, that is, two instances of the structure `DrinfeldDatum`: each consists of families $N_0, N_1$ of $\mathcal O$-submodules of $K^2$ indexed by $\operatorname{Spec} B$, each finitely generated and spanning $K^2$ over $K$, with $N_0(x) \le N_1(x)$ and $\pi N_1(x) \subseteq N_0(x)$ and with $\{x : v \in N_i(x)\}$ open for every $v \in K^2$, together with invertible $B$-modules $T_0, T_1$, $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by the image of $\pi$ in $B$, and, at each point $x$, surjective $B_x$-linear comparison maps $u_i(x) : B_x \otimes_{\mathcal O} N_i(x) \to (T_i)_x$ compatible with the inclusion $N_0(x) \le N_1(x)$ and $\Pi_0$, and with multiplication by $\pi$ and $\Pi_1$. The assertion is that the type `Q.Iso Q'` of isomorphisms from $Q$ to $Q'$ — data consisting of equalities $N_i(x) = N'_i(x)$ for all $x$ and $i \in \{0,1\}$, $B$-linear equivalences $\tau_i : T_i \xrightarrow{\sim} T'_i$ commuting with $\Pi_0$ and $\Pi_1$ and satisfying $u'_i(x)(1 \otimes v) = (\tau_i)_x(u_i(x)(1 \otimes v))$ for every point $x$ and every $v \in K^2$ lying in the relevant lattice — is a subsingleton: any two such isomorphisms are equal.
--
--   This is the rigidity statement for the Drinfeld data used in the Čerednik–Drinfeld uniformisation: a morphism between two such data over a base is unique if it exists, so the data form a category whose isomorphisms carry no automorphism ambiguity. It is cited in the construction of base change of Drinfeld data, where the transition equivalences $\tau$ are shown to be uniquely determined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_Iso_subsingleton.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.Iso.subsingleton
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q Q' : DrinfeldDatum (K := K) π B) : Subsingleton (Q.Iso Q') := by sorry
