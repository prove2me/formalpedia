-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic
-- name    : AlgebraicCurve.Pic0.eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/c83378cf-94b5-53bc-b1be-e291202f9518
-- title:
--   Frobenius characteristic polynomial equals the zeta numerator
-- statement:
--   Let $k$ be a finite field, $q=\#k$, let $K$ be an algebraically closed field, and let $F_0/k$ and $F/K$ be field extensions, together with an algebra map $F_0\to F$, such that each of $F_0$ over $k$ and $F$ over $K$ satisfies `IsCurveOver`: every nonzero function has a divisor, which has degree $0$; every place has residue field finite over the base field; and the module of Kähler differentials is free of rank one. Here a place is a valuation subring of the function field, different from the whole field, containing the base field and a principal ideal ring; divisors are finitely supported $\mathbb{Z}$-valued functions on places, $\deg$ is the sum of the coefficients weighted by the degrees $[\kappa(v):K]$ of the residue fields, and `Pic0` is the quotient of the degree-zero divisors by the divisors of nonzero functions. Assume: $F_0$ is generated over $k$ by a finite set; $F$ is generated over $K$ by the image of $F_0$; every $a\in K$ satisfies $a^{q^n}=a$ for some $n\ge 1$. Let $\varphi\colon F\to F$ be a $K$-algebra endomorphism whose underlying ring map is integral and which acts on the image of $F_0$ by $x\mapsto x^{q}$, and let $T$ be an endomorphism of the additive group $\mathrm{Pic}^0(F/K)$ inducing, on classes, push-forward of degree-zero divisors along $\varphi$. Let $g=$ `genusFF K F`, the $K$-dimension of $H^1$ of the zero divisor. Let $P_\pi\in\mathbb{Z}[X]$ be monic of degree $2g$ such that for every monic $G\in\mathbb{Z}[X]$ whose constant coefficient is nonzero in $K$: the kernel of $G(T)$ has cardinality $|\operatorname{Res}(G,P_\pi)|$ when $\operatorname{Res}(G,P_\pi)\neq 0$, and is infinite when $\operatorname{Res}(G,P_\pi)=0$. Let $P\in\mathbb{Z}[X]$ be monic of degree $2g$ such that for every $n\ge 1$ the number of places of $F/K$ fixed by the $n$-th iterate of the restriction map $w\mapsto \varphi^{-1}(\mathcal{O}_w)$ on places equals $q^{n}+1-\sum_i \omega_i^{\,n}$, the sum over the complex roots $\omega_i$ of $P$ with multiplicity. Then $P_\pi=P$.
--
--   This is the identification, in Weil's form, of the characteristic polynomial of the Frobenius endomorphism of the Jacobian — characterised through the orders $|\operatorname{Res}(G,P_\pi)|$ of the kernels of the separable endomorphisms $G(\pi)$ on $\mathrm{Pic}^0$ — with the numerator $X^{2g}L(1/X)$ of the zeta function of the function field, read off from the counts of rational places. It feeds the version of the statement recorded as [`AlgebraicCurve.Pic0.eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq`](thm.html#AlgebraicCurve.Pic0.eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq), and through it the Riemann hypothesis for curves over finite fields used in bounding traces of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.eq_of_natCard_ker_aeval_eq_natAbs_resultant_of_natCard_fixedPoints_restrictAlong_eq_of_isAlgebraic
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card k ^ n = a)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (T : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 K F)
    (hT : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      T (AlgebraicCurve.Pic0.mk D) =
        AlgebraicCurve.Pic0.mk ⟨AlgebraicCurve.Divisor.pushforwardAlong φ hφi D,
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩)
    (Pπ : Polynomial ℤ) (hπm : Pπ.Monic) (hπdeg : Pπ.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hπ : ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        (G.resultant Pπ ≠ 0 →
          Nat.card (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker =
            (G.resultant Pπ).natAbs) ∧
        (G.resultant Pπ = 0 →
          ¬ Finite (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker))
    (P : Polynomial ℤ) (hPm : P.Monic) (hPdeg : P.natDegree = 2 * AlgebraicCurve.genusFF K F)
    (hfix : ∀ n : ℕ, 0 < n →
      (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
        (Nat.card k : ℂ) ^ n + 1 - (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) :
    Pπ = P := by sorry
