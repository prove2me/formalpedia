-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_primaryComponent_ker_aeval_of_pushforwardAlong_frobenius
-- name    : AlgebraicCurve.Pic0.exists_monic_natCard_primaryComponent_ker_aeval_of_pushforwardAlong_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/b4323e8a-8a7d-57cf-9177-6b6bd34ed9be
-- title:
--   Frobenius polynomial on Pic⁰: place counts and ℓ-primary kernels
-- statement:
--   Let $k$ be a finite field, $K$ an algebraically closed field, and $F_0$, $F$ fields with $k \to F_0 \to F$ and $K \to F$ algebra structures, such that $F_0$ is a curve over $k$ and $F$ a curve over $K$ in the project's sense: principal divisors exist (every nonzero function has a divisor, of degree zero), every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one. Assume $F_0 = k(s)$ for a finite set $s \subseteq F_0$, that $F$ is generated over $K$ by the image of $F_0$, and let $\varphi \colon F \to F$ be a $K$-algebra endomorphism which is integral as a ring map and satisfies $\varphi(x) = x^{\,\#k}$ for $x$ in the image of $F_0$. Let $T$ be an additive endomorphism of $\mathrm{Pic}^0(F/K)$ — the group of degree-zero divisors, i.e. finitely supported $\mathbb{Z}$-valued functions on places (valuation subrings of $F$ containing $K$, proper, with principal ideals) of total degree zero, modulo those of functions — that sends the class of a degree-zero divisor $D$ to the class of its push-forward along $\varphi$. Then there exists a monic $P \in \mathbb{Z}[X]$ with $\deg P = 2\,g$, where $g = \mathrm{genusFF}(K,F) = \dim_K H^1(0)$, such that: (i) for every $n > 0$ the set of fixed points of the $n$-th iterate of the map $w \mapsto \varphi^{-1}(\mathcal{O}_w)$ on places of $F/K$ is finite, of cardinality $(\#k)^n + 1 - \sum_{\omega} \omega^n$, the sum over the complex roots $\omega$ of $P$ with multiplicity; and (ii) for every monic $G \in \mathbb{Z}[X]$ and every prime $\ell$ with $\ell \neq 0$ in $K$, if $\mathrm{Res}(G,P) \neq 0$ then the $\ell$-primary component of $\ker G(T)$ has cardinality $\ell^{v_\ell(|\mathrm{Res}(G,P)|)}$, while if $\mathrm{Res}(G,P) = 0$ then that $\ell$-primary component is infinite.
--
--   This is Weil's description of the Frobenius endomorphism of the Jacobian of a curve over a finite field: a single monic integral polynomial of degree $2g$ simultaneously computes the numbers of points of the curve over all finite extensions and, through resultants, the orders of $\ell$-primary kernels of $G(\mathrm{Frob})$ on the degree-zero divisor class group, so that $P$ is the characteristic polynomial of Frobenius on the $\ell$-adic Tate module for every $\ell$ invertible in $K$. It feeds the computation of traces of Frobenius on torsion of $\mathrm{Pic}^0$ used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_monic_natCard_primaryComponent_ker_aeval_of_pushforwardAlong_frobenius.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Pic0.exists_monic_natCard_primaryComponent_ker_aeval_of_pushforwardAlong_frobenius
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
          AlgebraicCurve.Divisor.pushforwardAlong_mem_degZero φ hφi D.2⟩) :
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * AlgebraicCurve.genusFF K F ∧
      (∀ n : ℕ, 0 < n →
        (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]).Finite ∧
        (Nat.card (Function.fixedPoints (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
          (Nat.card k : ℂ) ^ n + 1 -
            (((P.map (Int.castRingHom ℂ)).roots.map (fun z => z ^ n)).sum)) ∧
      ∀ (G : Polynomial ℤ), G.Monic → ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
        (G.resultant P ≠ 0 →
          Nat.card (AddCommGroup.primaryComponent
            (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ) =
            ℓ ^ ((G.resultant P).natAbs.factorization ℓ)) ∧
        (G.resultant P = 0 →
          ¬ Finite (AddCommGroup.primaryComponent
            (Polynomial.aeval (R := ℤ) T.toIntLinearMap G).toAddMonoidHom.ker ℓ)) := by sorry
