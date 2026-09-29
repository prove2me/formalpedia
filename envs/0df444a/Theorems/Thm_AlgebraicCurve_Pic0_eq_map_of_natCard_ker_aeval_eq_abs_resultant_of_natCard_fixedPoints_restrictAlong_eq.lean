-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_eq_map_of_natCard_ker_aeval_eq_abs_resultant_of_natCard_fixedPoints_restrictAlong_eq
-- name    : AlgebraicCurve.Pic0.eq_map_of_natCard_ker_aeval_eq_abs_resultant_of_natCard_fixedPoints_restrictAlong_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/fb9eda19-7892-5d69-82f4-85c5a4d27671
-- title:
--   Frobenius characteristic polynomial on Pic⁰ equals the zeta numerator
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and let $F_0$ be a $k$-algebra field and $F$ a field that is simultaneously a $K$-algebra and an $F_0$-algebra, with $F_0$ a curve over $k$ and $F$ a curve over $K$ in the sense of `IsCurveOver`: principal divisors exist (every nonzero function has a divisor of degree zero recording its orders at all places), every place has residue field finite over the constant field, and the module of Kähler differentials is free of rank one. Assume $F_0$ is generated over $k$ by a finite set, and that $F$ is generated over $K$ by the image of $F_0$. Let $\varphi : F \to F$ be a $K$-algebra endomorphism whose underlying ring map is integral and which acts on $F_0$ by $x \mapsto x^{q}$, $q = \operatorname{card} k$, i.e. $\varphi(\iota x) = \iota(x^{q})$ for $x \in F_0$. Let $T$ be an endomorphism of the additive group $\mathrm{Pic}^0(K,F)$ (degree-zero divisors modulo principal ones) that sends the class of a degree-zero divisor $D$ to the class of its push-forward along $\varphi$. Let $P_\pi \in \mathbb{Q}[X]$ be monic of degree $2\,g$, where $g = \operatorname{genusFF} K F = \dim_K H^1(0)$, and assume: for every monic $G \in \mathbb{Z}[X]$ whose constant coefficient is nonzero in $K$, if the resultant of the image of $G$ in $\mathbb{Q}[X]$ with $P_\pi$ is nonzero then the kernel of $G(T)$ has cardinality the absolute value of that resultant, while if the resultant vanishes the kernel is not finite. Let $P \in \mathbb{Z}[X]$ be monic of degree $2\,g$ such that for every $n > 0$ the number of fixed points of the $n$-th iterate of the restriction map $w \mapsto \varphi^{-1}(w)$ on places of $F/K$ equals, in $\mathbb{C}$, $q^{n} + 1 - \sum_{z} z^{n}$, the sum running with multiplicity over the complex roots of $P$. Then $P_\pi$ is the image of $P$ in $\mathbb{Q}[X]$.
--
--   This is the identification of the characteristic polynomial of the Frobenius push-forward on $\mathrm{Pic}^0$, a priori only rational, with the numerator $X^{2g}L(1/X)$ of the zeta function of the curve, over an arbitrary algebraically closed constant field; in particular that characteristic polynomial has integer coefficients. It feeds the statement [`AlgebraicCurve.Pic0.exists_mvPolynomial_eval_eq_natCard_ker_aeval_of_pushforwardAlong_frobenius`](thm.html#AlgebraicCurve.Pic0.exists_mvPolynomial_eval_eq_natCard_ker_aeval_of_pushforwardAlong_frobenius), and is the step that upgrades the rational-coefficient degree theory for $\mathbb{Z}[\mathrm{Fr}_*]$ to an integral one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_eq_map_of_natCard_ker_aeval_eq_abs_resultant_of_natCard_fixedPoints_restrictAlong_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.eq_map_of_natCard_ker_aeval_eq_abs_resultant_of_natCard_fixedPoints_restrictAlong_eq
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (Pπ : Polynomial ℚ) (hπm : Pπ.Monic) (hπdeg : Pπ.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hπ : ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        ((G.map (Int.castRingHom ℚ)).resultant Pπ ≠ 0 →
          ((Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker : ℕ) : ℚ) =
            |(G.map (Int.castRingHom ℚ)).resultant Pπ|) ∧
        ((G.map (Int.castRingHom ℚ)).resultant Pπ = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (P : Polynomial ℤ) (hPm : P.Monic) (hPdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    Pπ = P.map (Int.castRingHom ℚ) := by sorry
