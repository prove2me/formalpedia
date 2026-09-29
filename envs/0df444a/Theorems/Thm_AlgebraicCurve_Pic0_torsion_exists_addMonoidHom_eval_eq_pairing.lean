-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing
-- name    : AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/d61b222b-3e47-5b66-abe8-c7b60dbb1cb3
-- title:
--   Weil pairing as a homomorphism into the character group
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $n$ be a non-zero natural number; assume `HasPrincipalDivisors K F`, i.e. every non-zero $f \in F$ has an associated divisor of degree zero whose value at each place $v$ is $v.\mathrm{ord}(f)$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ and a principal ideal ring; divisors are finitely supported $\mathbb{Z}$-valued functions on places, $\mathrm{Pic}^0$ is the quotient of the degree-zero divisors by the principal ones, and $\mathrm{Pic}^0[n]$ is its $n$-torsion subgroup. Three hypotheses are assumed: Weil reciprocity $\mathrm{ev}_{D_g}(f) = \mathrm{ev}_{D_f}(g)$ for non-zero $f,g$ with divisors $D_f,D_g$ recording their orders, with $v.\mathrm{ord}(f)=0$ or $v.\mathrm{ord}(g)=0$ at every place and all places in either support rational (the structure map $K \to$ residue field being surjective); that a non-zero $u \in F$ with all orders zero lies in the image of $K$; and a moving hypothesis, that every class $x \in \mathrm{Pic}^0[n]$ and every finite set $S$ of places admits a degree-zero divisor representing $x$ whose support consists of rational places outside $S$. The conclusion asserts the existence of an additive homomorphism $\mathrm{hom}$ from $\mathrm{Pic}^0[n]$ to the additive copy of the group of $K$-valued additive characters of $\mathrm{Pic}^0[n]$ such that for every Weil datum $d$ of order $n$ — divisors $D_1,D_2$ and non-zero $f_1,f_2$ with $v.\mathrm{ord}(f_i) = n \cdot D_i(v)$ for all $v$, with $D_1(v)=0$ or $D_2(v)=0$ everywhere and every place in either support rational — and all $x,y \in \mathrm{Pic}^0[n]$: if $D_1$ is the underlying divisor of a degree-zero divisor whose class is $x$, and $D_2$ likewise for $y$, then the character $\mathrm{hom}(x)$ evaluated at $y$ equals $d$'s pairing value $\mathrm{ev}_{D_2}(f_1)/\mathrm{ev}_{D_1}(f_2)$.
--
--   This is the statement that the divisorial Weil pairing on the $n$-torsion of the Jacobian is well defined and additive in each variable, packaged as a map from $\mathrm{Pic}^0[n]$ into its group of $K$-valued characters (the Cartier dual), with no non-degeneracy asserted. It is the source of the existence results for Weil pairings on $\mathrm{Pic}^0[n]$, including the antisymmetric version and the construction of divisorial Weil pairing data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing.lean

import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_JacobianH1Autoduality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S)) :
    ∃ hom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n),
      ∀ (d : WeilDatum K F n) (x y : Pic0.torsion K F n),
        (∃ E : Divisor.degZero (K := K) (F := F), (E : Divisor K F) = d.D₁ ∧ Pic0.mk E = (x : Pic0 K F)) →
        (∃ E : Divisor.degZero (K := K) (F := F), (E : Divisor K F) = d.D₂ ∧ Pic0.mk E = (y : Pic0 K F)) →
        (Additive.toMul (hom x)) y = d.pairing := by sorry
