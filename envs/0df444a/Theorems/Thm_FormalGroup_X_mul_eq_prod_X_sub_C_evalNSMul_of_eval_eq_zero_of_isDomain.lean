-- Prove2me | Theorems.Thm_FormalGroup_X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain
-- name    : FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/a26b88ef-9dc2-52d3-b197-4f3033ccbb5c
-- title:
--   Full set of q-torsion points over a domain
-- statement:
--   Let $T$ be a commutative ring that is an integral domain, local and Noetherian, and complete (and separated) for the adic topology of its maximal ideal $\mathfrak m =$ `maximalIdeal T`. Let $F$ be a one-dimensional formal group law over $T$ which is commutative, and let $q$ be a prime number whose image in $T$ is nonzero. Suppose given a monic polynomial $g \in T[X]$ with `natDegree` equal to $q-1$ (natural subtraction) all of whose coefficients of index $< q-1$ lie in $\mathfrak m$, and a unit $v$ of $T[[X]]$, such that the $q$-th iterate series `F.nthSeries q` — defined recursively by `nthSeries 0 = 0` and `nthSeries (n+1) = F(nthSeries n, X)`, i.e. the multiplication-by-$q$ series $[q]_F$ — factors as $X \cdot g \cdot v$ in $T[[X]]$. Let finally $x \in \mathfrak m$ satisfy $g(x) = 0$. Then in $T[X]$ one has $$X \cdot g = \prod_{a=0}^{q-1}\bigl(X - C(\mathrm{F.evalNSMul}\,a\,x)\bigr),$$ where `F.evalNSMul` is defined recursively by `evalNSMul 0 x = 0` and `evalNSMul (n+1) x = F.eval (evalNSMul n x) x`, the evaluation `F.eval` being the substitution of two elements of $\mathfrak m$ into the two-variable series $F$ computed $\mathfrak m$-adically; thus the $a$-th factor is $X - [a]_F(x)$.
--
--   This is the "full set of sections" statement for the $q$-torsion of a formal group: the Igusa factor $g$, together with the factor $X$ accounting for the origin, has as its roots exactly the multiples $[a]_F(x)$, $0 \le a < q$, of a single root $x$, with multiplicities. It is used in the construction of Drinfeld bases on the formal completions occurring in the moduli-theoretic analysis of modular curves, where it is invoked for the domains obtained by adjoining a root of the relevant $q$-division polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime] (hq0 : (q : T) ≠ 0)
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (x : T) (hx : x ∈ maximalIdeal T) (hg : g.eval x = 0) :
    Polynomial.X * g = ∏ a ∈ Finset.range q, (Polynomial.X - Polynomial.C (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a x)) := by sorry
