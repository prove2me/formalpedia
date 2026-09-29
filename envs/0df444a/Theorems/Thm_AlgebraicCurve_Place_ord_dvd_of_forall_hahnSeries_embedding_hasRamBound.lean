-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
-- name    : AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/f165bcf6-81a8-5fab-9912-9eaa96ffdc12
-- title:
--   Bounded Puiseux denominators bound ramification over a closed point
-- statement:
--   Let $K$ be a field of characteristic $0$, let $L$ be an algebraically closed field which is a $K$-algebra, and let $F$ be a field equipped with $K$-algebra and $\mathrm{RatFunc}\,K$-algebra structures which are compatible (a scalar tower over $K$) and with $F$ finite-dimensional over $\mathrm{RatFunc}\,K$. Let $p \in K[X]$ be irreducible and let $a \in L$ satisfy $p(a) = 0$ and $p'(a) \neq 0$, so $a$ is a simple root of $p$ in $L$. Let $d$ be a natural number with $0 < d$. Assume that for every $K$-algebra homomorphism $\psi \colon F \to \mathrm{HahnSeries}\,\mathbb{Q}\,L$ sending the image of $X$ in $F$ to $\mathrm{C}(a) + t$ (the Hahn series $a$ plus the monomial with coefficient $1$ in degree $1$), and for every $x \in F$, the series $\psi(x)$ satisfies [`HahnSeries.HasRamBound d`](def/HahnSeries_RamificationBound.html#L32), i.e. its support is contained in the set of rationals $k/d$ with $k \in \mathbb{Z}$. Let $w$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F(K)$, different from $F$ itself, and a principal ideal ring; its order function is $w.\mathrm{ord}(f) = -\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the maximal ideal of that subring. If $w.\mathrm{ord}$ of the image of $p$ in $F$ is positive, then this order divides $d$ in $\mathbb{Z}$.
--
--   This is the Newton–Puiseux ramification criterion in the form used downstream: if all branches of the finite cover $F / K(X)$ above the closed point $p$, expanded as Hahn series in a local parameter $t = X - a$ at a simple root $a$ of $p$, have support in $\tfrac{1}{d}\mathbb{Z}$, then the ramification index of every place of $F$ above $p$ divides $d$ (the case $d = 1$ being unramifiedness). It is applied to modular curves, in the divisibility statements for $\mathrm{ord}$ of $j$ and of $j - 1728$ at places of the relevant function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_dvd_of_forall_hahnSeries_embedding_hasRamBound.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
    {K L F : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    {d : ℕ} (hd : 0 < d)
    (hF : ∀ ψ : F →ₐ[K] HahnSeries ℚ L,
      ψ (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
          = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) →
        ∀ x : F, HahnSeries.HasRamBound d (ψ x))
    (w : AlgebraicCurve.Place K F)
    (hw : 0 < w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p))) :
    w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p)) ∣ (d : ℤ) := by sorry
