-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one
-- name    : AlgebraicCurve.Place.ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/1452d09e-bb47-58b5-b71d-c7b7fa7ca35f
-- title:
--   Unramifiedness from integral Puiseux exponents at a simple root
-- statement:
--   Let $K$ be a field of characteristic $0$, let $L$ be an algebraically closed extension field of $K$, and let $F$ be a field equipped with compatible $K$- and $\mathrm{RatFunc}(K)$-algebra structures (a $K$-algebra tower) such that $F$ is finite-dimensional over the rational function field $\mathrm{RatFunc}(K) = K(X)$. Let $p \in K[X]$ be irreducible and let $a \in L$ be a simple root of $p$, in the sense that $p(a) = 0$ and $p'(a) \neq 0$. Assume that for every $K$-algebra homomorphism $\psi \colon F \to \mathrm{HahnSeries}\ \mathbb{Q}\ L$ (the Hahn field of series over $L$ with rational exponents) sending the image of $X$ in $F$ to $a + t$, i.e. to $\mathrm{C}\,a + \mathrm{single}\,1\,1$, one has, for every $x \in F$, that $\psi(x)$ satisfies $\mathrm{HasRamBound}\ 1$, that is, the support of $\psi(x)$ is contained in the image of $\mathbb{Z}$ in $\mathbb{Q}$ (no genuinely fractional exponents occur). Let $w$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F$'s image, different from $F$ itself and a principal ideal ring, and write $w.\mathrm{ord}(f) = -\mathrm{log}$ of the associated adic valuation of $f$. If $w.\mathrm{ord}$ of the image of $p$ in $F$ is positive, then it equals $1$.
--
--   This is the Newton–Puiseux unramifiedness criterion for a finite cover of the affine $X$-line: if every branch over $X = a$ expands as a Laurent series in $t$ with $X = a + t$ (no fractional exponents), then every place of $F$ lying over the closed point cut out by $p$ is unramified over $K(X)$. It is obtained from the Galois case by passing to a Galois closure and restricting places, and it is used in the analysis of orders of vanishing of $j$-values on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_eq_one_of_forall_hahnSeries_embedding_hasRamBound_one
    {K L F : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    (hF : ∀ ψ : F →ₐ[K] HahnSeries ℚ L,
      ψ (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
          = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) →
        ∀ x : F, HahnSeries.HasRamBound 1 (ψ x))
    (w : AlgebraicCurve.Place K F)
    (hw : 0 < w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p))) :
    w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p)) = 1 := by sorry
