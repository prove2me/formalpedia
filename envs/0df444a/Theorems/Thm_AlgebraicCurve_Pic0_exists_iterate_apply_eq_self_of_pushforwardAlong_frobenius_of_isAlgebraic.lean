-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_iterate_apply_eq_self_of_pushforwardAlong_frobenius_of_isAlgebraic
-- name    : AlgebraicCurve.Pic0.exists_iterate_apply_eq_self_of_pushforwardAlong_frobenius_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/65e9484d-ae94-50e3-9b20-b34f38e070cf
-- title:
--   Frobenius acts with finite orbits on places, divisors and Pic⁰
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0$, $F$ fields with $k$-algebra structure on $F_0$, $K$-algebra structure on $F$ and an $F_0$-algebra structure on $F$, such that $F$ is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero $f \in F$ admits a divisor whose coefficient at each place $v$ is $v.\mathrm{ord}(f)$ and whose degree is $0$, every place of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Assume $F_0$ is generated over $k$ by a finite subset, $F$ is generated over $K$ by the image of $F_0$, and every $a \in K$ satisfies $a^{(\#k)^n} = a$ for some $n > 0$. Let $\varphi : F \to F$ be a $K$-algebra map whose underlying ring map is integral and with $\varphi(x) = x^{\#k}$ on the image of $F_0$, and let $T$ be an additive endomorphism of $\mathrm{Pic}^0(F/K)$ sending the class of a degree-zero divisor $D$ to the class of its pushforward along $\varphi$. Then: every place $w$ of $F/K$ satisfies $(\mathrm{Place.restrictAlong}\ \varphi)^n(w) = w$, every divisor $D$ satisfies $(\mathrm{pushforwardAlong}\ \varphi)^n(D) = D$, and every $x \in \mathrm{Pic}^0(F/K)$ satisfies $T^n(x) = x$, each for some $n > 0$ depending on the argument.
--
--   This is the statement, in function-field language, that over an algebraic closure of a finite field every closed point, every divisor and every degree-zero divisor class of a curve is fixed by a positive power of the relative Frobenius, i.e. is defined over a finite subfield. It is the finiteness input used by [`AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic), where the $\ell$-primary part of $\mathrm{Pic}^0$ is exhausted by the kernels of the maps $T^n - 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_iterate_apply_eq_self_of_pushforwardAlong_frobenius_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.exists_iterate_apply_eq_self_of_pushforwardAlong_frobenius_of_isAlgebraic
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    (∀ w : AlgebraicCurve.Place K F, ∃ n : ℕ, 0 < n ∧
        (AlgebraicCurve.Place.restrictAlong φ hφi)^[n] w = w) ∧
    (∀ D : AlgebraicCurve.Divisor K F, ∃ n : ℕ, 0 < n ∧
        (⇑(AlgebraicCurve.Divisor.pushforwardAlong φ hφi))^[n] D = D) ∧
    (∀ x : AlgebraicCurve.Pic0 K F, ∃ n : ℕ, 0 < n ∧ (⇑T)^[n] x = x) := by sorry
