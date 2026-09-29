-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
-- name    : CerednikDrinfeld.FormalODModule.exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/76c2931c-f31e-5e8c-bc2e-b93756861605
-- title:
--   A power of p kills a nilpotently supported closed subscheme
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring in which the image of $p$ is nilpotent. Let $X$ be a formal $\mathcal O_D$-module over $B$ in the sense of the project's structure `FormalODModule`: a $2$-dimensional commutative formal group law $F$ over $B$, a map $\mathrm{act}$ from $\mathrm{Zp2}\ p = W(\mathbb F_{p^2})$ to pairs of power series in $B[\![x_0,x_1]\!]$ and a further such pair $\varpi$, subject to the requirements that every $\mathrm{act}(a)$ and $\varpi$ be endomorphisms of the law $F$ (constant coefficients zero and compatibility with $F$), $\mathrm{act}(1)$ be the identity pair, $\mathrm{act}(ab)=\mathrm{act}(a)\circ\mathrm{act}(b)$, $\mathrm{act}(a+b)$ be the sum of $\mathrm{act}(a)$ and $\mathrm{act}(b)$ formed via $F$, $\varpi\circ\varpi=\mathrm{act}(p)$, and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ for the Witt-vector Frobenius $\sigma$. Let $\rho=(\rho_0,\rho_1)$ be a pair of elements of $B[\![x_0,x_1]\!]$, and assume there is a $K$ such that $x_i^K$ lies in the ideal $(\rho_0,\rho_1)$ for $i=0,1$. Then there exists $N$ such that both coordinates of $\mathrm{act}(p^N)$, the multiplication-by-$p^N$ series of $X$, lie in $(\rho_0,\rho_1)$.
--
--   Geometrically: if the closed subscheme $\{\rho_0=\rho_1=0\}$ of the formal group underlying $X$ is supported at the origin (each coordinate nilpotent modulo $\rho$) and $p$ is nilpotent in the base, then that subscheme is contained in the kernel of $[p^N]_X$ for all large $N$; this replaces an appeal to "killed by its order" results. It is used in the Cerednik–Drinfeld formal $\mathcal O_D$-module theory, in the factorisation of an isogeny of given height through $[p^N]$, in the comparison of the ideals cut out by $\rho$ and by $\varpi$ for Atkin–Lehner quotients of fake elliptic curves, and in the admissible-cover statement for the moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_forall_act_pow_mem_span_of_isNilpotent_of_X_pow_mem
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B))
    (X : FormalODModule p B) (ρ : Series B)
    (hK : ∃ K : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ K ∈ Ideal.span (Set.range ρ)) :
    ∃ N : ℕ, ∀ i : Fin 2, X.act ((p : Zp2 p) ^ N) i ∈ Ideal.span (Set.range ρ) := by sorry
