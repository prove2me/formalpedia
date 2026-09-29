-- Prove2me | Theorems.Thm_FormalGroup_evalNSMul_mul_eq_zero_of_eval_eq_zero
-- name    : FormalGroup.evalNSMul_mul_eq_zero_of_eval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/e4cb0773-0e54-5f36-a61d-eaccc81acc60
-- title:
--   Roots of the Igusa factor are [q]_F-torsion
-- statement:
--   Let $T$ be a commutative Noetherian local ring, complete (and separated) for the adic topology of its maximal ideal $\mathfrak m =$ `maximalIdeal T`, let $F$ be a one-dimensional formal group law over $T$ satisfying `F.IsComm`, and let $q$ be a prime. Assume given: a monic polynomial $g \in T[X]$ whose `natDegree` is $q-1$ and all of whose coefficients in degrees $i < q-1$ lie in $\mathfrak m$; a unit $v$ of $T[[X]]$; and a factorisation `F.nthSeries q` $= X \cdot g \cdot v$ in $T[[X]]$, where `F.nthSeries` is defined by `nthSeries 0 = 0` and `nthSeries (n+1) =` the substitution of (`nthSeries n`, $X$) into the two-variable series of $F$, so that `F.nthSeries q` is the $q$-series $[q]_F$. Assume further that $x \in \mathfrak m$ satisfies $g(x) = 0$, and let $a$ be a natural number. Then, evaluation being taken with respect to the $\mathfrak m$-adic structure on $T$, one has `F.evalNSMul q (F.evalNSMul a x)` $= 0$, where `F.evalNSMul` is given by `evalNSMul 0 x = 0` and `evalNSMul (n+1) x = F.eval (evalNSMul n x) x`, i.e. the $n$-fold $F$-sum; that is, $[q]_F\bigl([a]_F(x)\bigr) = 0$.
--
--   This is the torsion half of the statement that the roots in $\mathfrak m$ of the Igusa factor $g$ of the $q$-series of a formal group of height one are $[q]_F$-torsion points, in the style of the analysis of $[p]$-series of formal groups over complete local rings. It is used in the proof that $X \cdot \prod (X - [a]_F(x))$ computes the $q$-series over a domain, via [`FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain`](thm.html#FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_evalNSMul_mul_eq_zero_of_eval_eq_zero.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.evalNSMul_mul_eq_zero_of_eval_eq_zero
    (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (x : T) (hx : x ∈ maximalIdeal T) (hg : g.eval x = 0) (a : ℕ) :
    (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul q (F.evalNSMul a x)) = 0 := by sorry
