-- Prove2me | Theorems.Thm_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
-- name    : FormalGroup.exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/9f34a167-937a-5375-978e-d8a0a2c5575c
-- title:
--   Unit times X^q criterion for [q]_F via g(0)=0
-- statement:
--   Let $T$ be a commutative local ring with maximal ideal $\mathfrak m$, let $F$ be a one-dimensional formal group law over $T$ satisfying the commutativity predicate `IsComm`, and let $q$ be a prime number. Here `F.nthSeries` is the sequence of one-variable power series defined by $[0]=0$ and $[n+1](X)=F([n](X),X)$, so that `F.nthSeries q` is the multiplication-by-$q$ series of $F$. Assume given a monic polynomial $g \in T[X]$ whose `natDegree` equals $q-1$ and all of whose coefficients of index $i < q-1$ lie in $\mathfrak m$, together with a power series $v \in T[\![X]\!]$ that is a unit, such that the factorisation $[q](X) = X \cdot g(X) \cdot v(X)$ holds in $T[\![X]\!]$, where $g$ is viewed as a power series. The conclusion is the conjunction of two equivalences: first, there exists a unit $u \in T[\![X]\!]$ with $[q](X) = u(X) X^q$ if and only if $g$ evaluated at $0$ vanishes; and second, $g(0) = 0$ if and only if the image of $q$ in $T$ is zero.
--
--   This is the criterion, at the origin, for the multiplication-by-$q$ series of a formal group over a local ring to be totally inseparable, i.e. a unit multiple of $X^q$, and it identifies this situation with the base having characteristic $q$. It is the $x = 0$ instance of the Igusa-type generator criterion and is used in [`FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain`](thm.html#FormalGroup.X_mul_eq_prod_X_sub_C_evalNSMul_of_eval_eq_zero_of_isDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero.lean

import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.exists_nthSeries_eq_mul_X_pow_iff_eval_zero_eq_zero
    (T : Type*) [CommRing T] [IsLocalRing T]
    (F : FormalGroup T) [F.IsComm] (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v) :
    ((∃ u : PowerSeries T, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ q) ↔ g.eval 0 = 0) ∧
      (g.eval 0 = 0 ↔ (q : T) = 0) := by sorry
