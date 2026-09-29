-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N0_eq_of_not_mem_stratum
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.N0_eq_of_not_mem_stratum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/6c954027-db5d-5caf-acdc-c76fd47c5595
-- title:
--   Off the opposite stratum, N₀ = pN₁ or N₀ = N₁
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring equipped with a $\mathbb{Z}_p$-algebra structure, and let $Q$ be a Drinfeld datum over $B$ for the field $K = \mathbb{Q}_p$ and the element $\pi = p \in \mathbb{Z}_p$: thus $Q$ assigns to every point $x \in \operatorname{Spec} B$ two $\mathbb{Z}_p$-submodules $N_0(x) \subseteq N_1(x)$ of $\mathbb{Q}_p^2$, each finitely generated and spanning $\mathbb{Q}_p^2$ over $\mathbb{Q}_p$, with $p\,N_1(x) \subseteq N_0(x)$ and with the sets $\{x : v \in N_i(x)\}$ open for every $v$, together with invertible $B$-modules $T_0, T_1$, $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by $p$, localised trivialisations $u_i$ of the base-changed lattices by the stalks of $T_i$ compatible with the inclusion $N_0(x) \subseteq N_1(x)$ and with multiplication by $p$, and the remaining fields of the structure (the strata `stratum₀`, `stratum₁` and the injectivity conditions). Let $x \in \operatorname{Spec} B$. The conclusion is a conjunction: if $x \notin Q.\mathrm{stratum}_1$, then a vector $v \in \mathbb{Q}_p^2$ lies in $N_0(x)$ if and only if $v = p\,w$ for some $w \in N_1(x)$; and if $x \notin Q.\mathrm{stratum}_0$, then $N_0(x) = N_1(x)$.
--
--   This is the lattice-theoretic description of a Drinfeld datum away from the two strata of $\operatorname{Spec} B$: off the stratum attached to $\Pi_1$ the smaller lattice is exactly $p$ times the larger, and off the stratum attached to $\Pi_0$ the two lattices coincide. It is used in the comparison of Drinfeld data under base change, via [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.N_eq_of_le_of_mem_stratum_iff`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.N_eq_of_le_of_mem_stratum_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_N0_eq_of_not_mem_stratum.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega LT.LatticeTree

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.N0_eq_of_not_mem_stratum
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [Algebra ℤ_[p] B]
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (x : PrimeSpectrum B) :
    (x ∉ Q.stratum₁ → ∀ v, v ∈ Q.N₀ x ↔ ∃ w ∈ Q.N₁ x, v = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w) ∧
    (x ∉ Q.stratum₀ → Q.N₀ x = Q.N₁ x) := by sorry
