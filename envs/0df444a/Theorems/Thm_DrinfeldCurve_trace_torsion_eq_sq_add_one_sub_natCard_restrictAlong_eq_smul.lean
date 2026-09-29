-- Prove2me | Theorems.Thm_DrinfeldCurve_trace_torsion_eq_sq_add_one_sub_natCard_restrictAlong_eq_smul
-- name    : DrinfeldCurve.trace_torsion_eq_sq_add_one_sub_natCard_restrictAlong_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/81c30eaa-525a-5d60-8192-b7ee7f0e2718
-- title:
--   Twisted Lefschetz trace formula on Pic⁰[ℓ^m] of the Drinfeld curve
-- statement:
--   Let $q$ be a prime and let $k$ be an algebraically closed field equipped with an algebra structure over $\mathrm{GF}(q^2)$, such that the coordinate ring `CoordRing q k` (the quotient of the polynomial ring in two variables over $k$ by the Drinfeld ideal) is a domain, and such that its fraction field $F =$ `drinfeldFunctionField q k` is a curve over $k$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): divisors of degree zero that are principal are detected by `HasPrincipalDivisors`, every place of $F$ over $k$ has residue field finite over $k$, and $\Omega[F/k]$ is free of rank one over $F$. Let $\varphi$ be a $k$-algebra endomorphism of $F$ whose underlying ring map is integral and which raises the images of the two coordinates $x$ and $y$ to the power $q^2$. Let $h$ lie in `hSubgroup q`, the kernel of `hChar q` inside $\mathrm{GL}_2(\mathbb{Z}/q) \times \mathrm{GF}(q^2)^\times$, acting on $F$ by the $k$-algebra automorphism `hFunctionFieldAction q k h`. Let $T$ be an additive endomorphism of $\mathrm{Pic}^0(F/k)$ — the quotient of the group of degree-zero divisors by the principal ones — which on the class of every degree-zero divisor $D$ is given by $T[D] = h^{-1}\cdot[\varphi_* D]$, where $\varphi_*$ is the pushforward of divisors along $\varphi$. Let $\ell$ be a prime different from $q$, let $m > 0$, and let $T_m$ be a $\mathbb{Z}/\ell^m$-linear endomorphism of the $\ell^m$-torsion subgroup of $\mathrm{Pic}^0(F/k)$ whose values agree with those of $T$ after inclusion into $\mathrm{Pic}^0(F/k)$. Then the trace of $T_m$ over $\mathbb{Z}/\ell^m$ equals $q^2 + 1$ minus the cardinality, reduced modulo $\ell^m$, of the set of places $w$ of $F$ over $k$ with $\varphi$-restriction `Place.restrictAlong φ hφi w` equal to $h \cdot w$.
--
--   This is the twisted Weil–Lefschetz trace formula for the Drinfeld (Deligne–Lusztig) curve: the trace of the twisted Frobenius correspondence $h^{-1}\circ\varphi_*$ on $\ell^m$-torsion of the degree-zero divisor class group computes the number of places fixed by the $h$-twisted Frobenius. It is obtained from the general trace formula [`AlgebraicCurve.Pic0.trace_pow_torsion_eq_of_pushforwardAlong`](thm.html#AlgebraicCurve.Pic0.trace_pow_torsion_eq_of_pushforwardAlong) together with the descent statement `exists_isCurveOver_adjoin_range_eq_top_apply_hFunctionFieldAction_eq_pow` exhibiting $\varphi\circ h$ as the relative $q^2$-Frobenius of an $\mathbb{F}_{q^2}$-form of $F$, and is used by [`DrinfeldCurve.cast_mul_trace_eq_natCard_restrictAlong_eq_smul_sub`](thm.html#DrinfeldCurve.cast_mul_trace_eq_natCard_restrictAlong_eq_smul_sub).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_trace_torsion_eq_sq_add_one_sub_natCard_restrictAlong_eq_smul.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem DrinfeldCurve.trace_torsion_eq_sq_add_one_sub_natCard_restrictAlong_eq_smul
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsAlgClosed k]
    [IsDomain (CoordRing q k)] [AlgebraicCurve.IsCurveOver k (drinfeldFunctionField q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (hφi : φ.toRingHom.IsIntegral)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ 2)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ 2)
    (h : hSubgroup q)
    (T : AlgebraicCurve.Pic0 k (drinfeldFunctionField q k) →+ AlgebraicCurve.Pic0 k (drinfeldFunctionField q k))
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := k) (F := drinfeldFunctionField q k),
      T (AlgebraicCurve.Pic0.mk D) =
        (hFunctionFieldAction q k h)⁻¹ • AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ q) (m : ℕ) (hm : 0 < m)
    (Tm : AlgebraicCurve.Pic0.torsion k (drinfeldFunctionField q k) (ℓ ^ m) →ₗ[ZMod (ℓ ^ m)]
      AlgebraicCurve.Pic0.torsion k (drinfeldFunctionField q k) (ℓ ^ m))
    (hTm : ∀ P : AlgebraicCurve.Pic0.torsion k (drinfeldFunctionField q k) (ℓ ^ m),
      ((Tm P : AlgebraicCurve.Pic0.torsion k (drinfeldFunctionField q k) (ℓ ^ m)) :
        AlgebraicCurve.Pic0 k (drinfeldFunctionField q k)) = T P) :
    LinearMap.trace (ZMod (ℓ ^ m)) (AlgebraicCurve.Pic0.torsion k (drinfeldFunctionField q k) (ℓ ^ m)) Tm =
      (q : ZMod (ℓ ^ m)) ^ 2 + 1 -
        (Nat.card {w : AlgebraicCurve.Place k (drinfeldFunctionField q k) //
            AlgebraicCurve.Place.restrictAlong φ hφi w = hFunctionFieldAction q k h • w} : ZMod (ℓ ^ m)) := by sorry
