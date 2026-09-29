-- Prove2me | Theorems.Thm_ArithmeticE_ordinary_cyclic_combination
-- name    : ArithmeticE.ordinary_cyclic_combination
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:34:54.90424+00:00
-- url     : https://prove2.me/theorems/07fe403c-3455-47df-9abc-b2c10241c9b1
-- title:
--   Ordinary cyclic scalar equation with prescribed algebraic initial coefficients
-- statement:
--   Let $f=(f_1,\ldots,f_m)$ be formal power series whose coefficients are algebraic over $\mathbb Q$, satisfying $Tf'=Bf$ with rational polynomial $T$ and $B$. Suppose a polynomial relation basis with a polynomial left inverse is available. Let $\xi$ be algebraic with $T(\xi)\ne0$, and let $a$ be an algebraic covector that is not the specialization of a polynomial relation among the $f_i$.
--
--   There exist polynomials $P_i$ with algebraic coefficients and a positive-order minimal scalar equation for $F=\sum_iP_if_i$ such that
--   $$P_i(\xi)=a_i,\qquad p_n(\xi)\ne0,$$
--   where $p_n$ is its leading coefficient. Thus the minimal equation is ordinary at $\xi$.
--
--   This is the algebraic cyclic-vector construction inside Beukers' proof, separated from the arithmetic zero theorem. It requires coefficient descent, finite-dimensional relation spaces, prescribed polynomial derivatives, and the determinant construction of the scalar equation. This statement is an open formalization obligation, not a conjectural mathematical claim. No value-zero hypothesis or E-arithmetic bound is used here.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. Theorem 3.2, construction of conditions (i)–(iii), pp. 6–7. The relation-basis input is separately proved.

import Definitions.Def_beukersLiftingData
open ArithmeticE

theorem ArithmeticE.ordinary_cyclic_combination
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hcoeff : ∀ i n, IsAlgebraic ℚ (PowerSeries.coeff n (f i)))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ) * f j)
    (hbasis : RelationBasis f)
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ) (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hnot : ¬ ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i : PowerSeries ℂ) * f i = 0) ∧ ∀ i, (p i).eval ξ = a i) :
    ∃ (P : Fin m → Polynomial ℂ) (p : ℕ → Polynomial ℂ) (n : ℕ),
      (∀ i k, IsAlgebraic ℚ ((P i).coeff k)) ∧
      (∀ i, (P i).eval ξ = a i) ∧ 0 < n ∧
      MinimalEquation p n (∑ i, (P i : PowerSeries ℂ) * f i) ∧ (p n).eval ξ ≠ 0 := by sorry
