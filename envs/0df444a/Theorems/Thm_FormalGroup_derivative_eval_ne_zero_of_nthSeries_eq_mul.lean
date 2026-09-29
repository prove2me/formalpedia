-- Prove2me | Theorems.Thm_FormalGroup_derivative_eval_ne_zero_of_nthSeries_eq_mul
-- name    : FormalGroup.derivative_eval_ne_zero_of_nthSeries_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/08b121fe-92db-532f-b28e-2dfcc19b1edb
-- title:
--   Zeros of the [q]-series in mathfrak m_V are simple
-- statement:
--   Let $q$ be a natural number and let $V$ be a commutative ring which is a domain and a local ring, complete and separated for the adic topology of its maximal ideal $\mathfrak m_V$, and suppose the image of $q$ in $V$ is nonzero. Let $G$ be a one-dimensional formal group law over $V$, equipped with a commutativity instance, and write `G.nthSeries` for the iterated series defined by `G.nthSeries 0 = 0` and `G.nthSeries (n+1) =` the substitution of `(G.nthSeries n, X)` into the two-variable power series of $G$, so that `G.nthSeries q` is the multiplication-by-$q$ series $[q]_G$. Assume given a polynomial $P \in V[Z]$ and a power series $U \in V[[Z]]$ which is a unit, such that $[q]_G = P \cdot U$ in $V[[Z]]$, the polynomial $P$ being viewed as a power series. Then for every $r \in \mathfrak m_V$ with $P(r) = 0$, the derivative satisfies $P'(r) \neq 0$.
--
--   This is the simplicity of the roots in $\mathfrak m_V$ of a Weierstrass-type factor of the multiplication-by-$q$ series of a formal group in residue characteristic prime to $q$ (étaleness of $q$-torsion), in the style of the Lubin–Tate analysis of formal groups over complete local rings. It is used in the construction of a Drinfeld-type adic basis, where it yields distinctness of the torsion points produced by such a factorisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_derivative_eval_ne_zero_of_nthSeries_eq_mul.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.derivative_eval_ne_zero_of_nthSeries_eq_mul
    (q : ℕ) {V : Type*} [CommRing V] [IsDomain V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (hqV : (q : V) ≠ 0) (G : FormalGroup V) [G.IsComm]
    (P : Polynomial V) (U : PowerSeries V) (hU : IsUnit U)
    (hq : G.nthSeries q = (P : PowerSeries V) * U)
    (r : V) (hr : r ∈ maximalIdeal V) (hPr : P.eval r = 0) :
    (Polynomial.derivative P).eval r ≠ 0 := by sorry
