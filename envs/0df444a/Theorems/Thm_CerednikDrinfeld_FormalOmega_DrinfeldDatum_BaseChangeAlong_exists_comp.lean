-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_comp
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/995090cc-3e8a-53bd-9470-2ecf463a2564
-- title:
--   Composition of base-change witnesses for Drinfeld data
-- statement:
--   Fix a commutative ring $\mathcal O$, a field $K$ that is an $\mathcal O$-algebra, an element $\pi \in \mathcal O$, and commutative $\mathcal O$-algebras $B$, $B'$, $B''$ together with $\mathcal O$-algebra homomorphisms $g \colon B \to B'$ and $h \colon B' \to B''$. Let $Q$, $Q'$, $Q''$ be Drinfeld data for $(\pi, K)$ over $B$, $B'$, $B''$ respectively, and let $W$ be a witness that $Q'$ is the base change of $Q$ along $g$ and $W'$ a witness that $Q''$ is the base change of $Q'$ along $h$; such a witness along $f$ consists of the identities $Q'.N_i(x') = Q.N_i(f^{-1}x')$ for $i = 0,1$ and all primes $x'$ of the target, of $f$-semilinear maps $\tau_0 \colon Q.T_0 \to Q'.T_0$ and $\tau_1 \colon Q.T_1 \to Q'.T_1$ whose ranges span the targets over the target ring, of the compatibilities $\tau_1 \circ \mathrm{Pi}_0 = \mathrm{Pi}_0 \circ \tau_0$ and $\tau_0 \circ \mathrm{Pi}_1 = \mathrm{Pi}_1 \circ \tau_1$, and of the clauses stating that if the stalk trivialisation of $Q$ at $f^{-1}x'$ sends $1 \otimes v$ to $t/s$, then that of $Q'$ at $x'$ sends $1 \otimes v$ to $\tau_i(t)/f(s)$. The conclusion is the existence of a witness $W''$ that $Q''$ is the base change of $Q$ along $h \circ g$ whose semilinear maps satisfy $W''.\tau_0(t) = W'.\tau_0(W.\tau_0(t))$ and $W''.\tau_1(t) = W'.\tau_1(W.\tau_1(t))$ for all $t$.
--
--   This is the composition law underlying the functoriality of Drinfeld's functor of quadruples, recorded for witnesses of the relation "is the base change along" so that composite comparison maps are available explicitly. It is used in the Zariski gluing of Drinfeld data, in [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap), where the $\tau$'s of different chains of witnesses must be compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_comp.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {B'' : Type} [CommRing B''] [Algebra 𝒪 B''] (g : B →ₐ[𝒪] B') (h : B' →ₐ[𝒪] B'')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'} {Q'' : DrinfeldDatum (K := K) π B''}
    (W : Q.BaseChangeAlong g Q') (W' : Q'.BaseChangeAlong h Q'') :
    ∃ W'' : Q.BaseChangeAlong (h.comp g) Q'',
      (∀ t, W''.τ₀ t = W'.τ₀ (W.τ₀ t)) ∧ (∀ t, W''.τ₁ t = W'.τ₁ (W.τ₁ t)) := by sorry
