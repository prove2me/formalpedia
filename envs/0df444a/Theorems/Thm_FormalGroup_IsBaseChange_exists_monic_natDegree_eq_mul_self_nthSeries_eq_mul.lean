-- Prove2me | Theorems.Thm_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
-- name    : FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/262d8b1c-244d-520b-aebe-d5af8cd11373
-- title:
--   Weierstrass preparation of the q-series of a formal group lift
-- statement:
--   Fix a natural number $q$, a field $k$, and a local ring $W_0$ that is adically complete for its maximal ideal, together with a ring homomorphism $\mathrm{res}_0 : W_0 \to k$ assumed surjective and with $\ker(\mathrm{res}_0) = \mathfrak m_{W_0}$. Let $F_0$ be a one-dimensional formal group law over $k$ satisfying `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. with respect to the ideal $\bot$ of $k$ there is a unit power series $u$ with $F_0.\mathtt{nthSeries}\ q = u \cdot F_0.\mathtt{drinfeldDivisor}\ q\ 0\ 0$, where $\mathtt{nthSeries}$ is the multiplication-by-$n$ series defined recursively by $[0] = 0$ and $[n+1] = F(\,[n],\,X\,)$. Let $F^u$ be a formal group law over $S = W_0[[t]]$ which is a lift of $F_0$ along $\theta = \mathrm{res}_0 \circ \mathrm{constantCoeff}$, in the sense that the power series of $F_0$ is the image under $\theta$, coefficientwise, of the power series of $F^u$. Then there are a polynomial $P \in S[Z]$ and a power series $U \in S[[Z]]$ with $P$ monic of degree $q^2$, all coefficients of $P$ of index $< q^2$ lying in $\mathfrak m_S$, $U$ a unit, and $F^u.\mathtt{nthSeries}\ q = P \cdot U$.
--
--   This is the Weierstrass preparation of the multiplication-by-$q$ series of a lift to $W_0[[t]]$ of a formal group over $k$ whose $q$-series is a unit times $Z^{q^2}$: the $q$-series factors as a distinguished polynomial of degree $q^2$ times a unit. It feeds the constructions of rings representing the $q$-division points of such a lift, and thereby the finiteness statements about them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsBaseChange_exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsBaseChange.exists_monic_natDegree_eq_mul_self_nthSeries_eq_mul
    (q : ℕ) (k : Type) [Field k]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀] [IsAdicComplete (maximalIdeal W₀) W₀]
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀))
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀) :
    ∃ (P : Polynomial (PowerSeries W₀)) (U : PowerSeries (PowerSeries W₀)),
      P.Monic ∧ P.natDegree = q * q ∧
      (∀ i : ℕ, i < q * q → P.coeff i ∈ maximalIdeal (PowerSeries W₀)) ∧
      IsUnit U ∧ Fu.nthSeries q = (P : PowerSeries (PowerSeries W₀)) * U := by sorry
