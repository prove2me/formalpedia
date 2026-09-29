-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_trace_pow_torsion_eq_of_pushforwardAlong
-- name    : AlgebraicCurve.Pic0.trace_pow_torsion_eq_of_pushforwardAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/cf368514-e3d3-5769-92f9-a369a77895e4
-- title:
--   Levelwise Lefschetz trace formula for Frobenius on Pic⁰[ℓ^m]
-- statement:
--   Let $k$ be a finite field and $K$ an algebraically closed field, and let $F_0$ be a field with a $k$-algebra structure and $F$ a field with compatible $K$- and $F_0$-algebra structures, both $F_0/k$ and $F/K$ satisfying `IsCurveOver`: every nonzero element has a divisor recording its orders at all places and having degree zero, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one. Assume $F_0$ is generated over $k$ by a finite set, and that $K$ together with the image of $F_0$ generates $F$. Let $\varphi\colon F\to F$ be a $K$-algebra endomorphism which is integral as a ring map and which acts on $F_0$ by $x\mapsto x^{\#k}$. Let $\ell$ be a prime with $\ell\neq 0$ in $K$, let $m>0$, and let $T$ be a $\mathbb Z/\ell^m$-linear endomorphism of the $\ell^m$-torsion subgroup of $\mathrm{Pic}^0(F/K)$ (degree-zero divisors modulo principal ones) such that for every degree-zero divisor $D$ with $\ell^m$-torsion class, $T$ sends that class to the class of the push-forward $\varphi_*D$. Then for every $n>0$, $\operatorname{tr}_{\mathbb Z/\ell^m}(T^n)=(\#k)^n+1-\#\{w : \mathrm{Fr}^n(w)=w\}$ in $\mathbb Z/\ell^m$, where $\mathrm{Fr}$ sends a place $w$ of $F/K$ to the place with valuation ring $\varphi^{-1}(\mathcal O_w)$.
--
--   This is the Lefschetz fixed-point (Weil) trace formula for the Frobenius push-forward on the degree-zero divisor class group of a function field over an algebraically closed field, stated one level at a time, modulo $\ell^m$, for an arbitrary $\mathbb Z/\ell^m$-linear operator implementing the push-forward on $\ell^m$-torsion; the fixed points of the $n$-fold iterate of $\mathrm{Fr}$ count the points of the underlying curve over the field with $(\#k)^n$ elements. It is used in the analysis of Drinfeld curves, where it yields the trace of Frobenius in terms of point counts and the resulting divisibility and principality statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_trace_pow_torsion_eq_of_pushforwardAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.trace_pow_torsion_eq_of_pushforwardAlong
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (m : ℕ) (hm : 0 < m)
    (T : AlgebraicCurve.Pic0.torsion K F (ℓ ^ m) →ₗ[ZMod (ℓ ^ m)]
      AlgebraicCurve.Pic0.torsion K F (ℓ ^ m))
    (hT : ∀ (D : AlgebraicCurve.Divisor.degZero (K := K) (F := F))
      (hD : AlgebraicCurve.Pic0.mk D ∈ AlgebraicCurve.Pic0.torsion K F (ℓ ^ m)),
      ((T ⟨AlgebraicCurve.Pic0.mk D, hD⟩ : AlgebraicCurve.Pic0.torsion K F (ℓ ^ m)) :
          AlgebraicCurve.Pic0 K F) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (n : ℕ) (hn : 0 < n) :
    LinearMap.trace (ZMod (ℓ ^ m)) (AlgebraicCurve.Pic0.torsion K F (ℓ ^ m)) (T ^ n) =
      (Nat.card k : ZMod (ℓ ^ m)) ^ n + 1 -
        (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) :
          ZMod (ℓ ^ m)) := by sorry
