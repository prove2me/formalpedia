-- Prove2me | Theorems.Thm_DrinfeldCurve_LocalChart_isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime
-- name    : DrinfeldCurve.LocalChart.isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/9cf31082-5b27-5185-b550-9d818589fe40
-- title:
--   Branch-prime pull-back along a chart automorphism with linear part c₁g
-- statement:
--   Let $q$ be a prime and let $W$ be a complete discrete valuation ring (a domain, complete for the adic topology of its maximal ideal) with $\mathfrak m_W=(\pi)$ and $q\in\mathfrak m_W$. Fix $c\in\mathfrak m_W$ with $c\neq 0$, and $f,u,v\in W[[X_0,X_1]]$ with $u,v$ units and $f-(X_0X_1^{\,q}-X_0^{\,q}X_1)\in(X_0,X_1)^{q+2}$; put $S:=W[[X_0,X_1]]/(C(c)\,v-f\,u)$ with quotient map $\mathrm{mkS}$. Let $\theta$ be a ring automorphism of $S$ fixing $\mathrm{mkS}(C(w))$ for every $w\in W$, and let $M\in\mathrm{Mat}_{2\times2}(W)$ satisfy $\theta(\mathrm{mkS}(X_j))-\mathrm{mkS}\big(\sum_i C(M_{ij})X_i\big)\in\big(\mathrm{mkS}(X_0),\mathrm{mkS}(X_1)\big)^2$ for $j=0,1$. Suppose $c_1\in W\setminus\mathfrak m_W$ and $g\in\mathrm{SL}_2(\mathbb Z)$ are such that $M_{ij}-c_1\,g_{ij}\in\mathfrak m_W$ for all $i,j$. Let $P\subset S$ be a prime ideal with $\mathrm{mkS}(X_0)\notin P$ or $\mathrm{mkS}(X_1)\notin P$, with $\mathrm{mkS}(C(\pi))\in P$, and such that for some integers $a,b,A,B$ with $A\equiv g_{00}a+g_{01}b$ and $B\equiv g_{10}a+g_{11}b$ modulo $q$ one has $\mathrm{mkS}(C(A)X_0+C(B)X_1+h)\in P$ for some $h\in(X_0,X_1)^2$. Then the contraction $\theta^{-1}(P)$ is prime, does not contain $\mathrm{mkS}(X_0)$ or does not contain $\mathrm{mkS}(X_1)$, contains $\mathrm{mkS}(C(\pi))$, and contains $\mathrm{mkS}(C(a)X_0+C(b)X_1+h')$ for some $h'\in(X_0,X_1)^2$.
--
--   This is the chart-algebra form of the statement that an automorphism of a Drinfeld chart ring whose linear part is $c_1g$ permutes the branch primes of the special fibre according to the action of $g$ on lines, so that contracting along the automorphism undoes $g$; it is phrased with the inverse image, so no uniqueness of branch primes is used. It is invoked by the lemmas on level automorphisms and Ogg-type profiles at auxiliary level used in constructing a regular model of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DrinfeldCurve_LocalChart_isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem DrinfeldCurve.LocalChart.isPrime_comap_and_exists_linear_add_mem_comap_of_ringEquiv_linearPart_of_branchPrime
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (c : W) (hc : c ∈ IsLocalRing.maximalIdeal W) (hc0 : c ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))

    (θ : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}) ≃+*
      (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u}))
    (hθW : ∀ w : W, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C w)) =
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C w))

    (M : Matrix (Fin 2) (Fin 2) W)
    (hθM : ∀ jj : Fin 2, θ (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X jj)) -
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1)}) ^ 2)

    (c₁ : W) (hc₁ : c₁ ∉ IsLocalRing.maximalIdeal W) (g : SL(2, ℤ))
    (hMg : ∀ ii jj : Fin 2, M ii jj - c₁ * ((g ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W)

    (P : Ideal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})) (hP : P.IsPrime)
    (hPX : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 0) ∉ P ∨
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.X 1) ∉ P)
    (hPπ : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u}) (MvPowerSeries.C π) ∈ P)

    (a b A B : ℤ)
    (hA : (q : ℤ) ∣ A - ((g 0 0 : ℤ) * a + (g 0 1 : ℤ) * b))
    (hB : (q : ℤ) ∣ B - ((g 1 0 : ℤ) * a + (g 1 1 : ℤ) * b))
    (hAB : ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
      Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u})
        (MvPowerSeries.C ((A : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((B : ℤ) : W) * MvPowerSeries.X 1 + h) ∈ P) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C c * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C c * v - f * u})
    (P.comap (θ : S →+* S)).IsPrime ∧
    (mkS (MvPowerSeries.X 0) ∉ P.comap (θ : S →+* S) ∨ mkS (MvPowerSeries.X 1) ∉ P.comap (θ : S →+* S)) ∧
    mkS (MvPowerSeries.C π) ∈ P.comap (θ : S →+* S) ∧
    ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
      mkS (MvPowerSeries.C ((a : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b : ℤ) : W) * MvPowerSeries.X 1 + h) ∈
        P.comap (θ : S →+* S) := by sorry
