-- Prove2me | Theorems.Thm_ArithmeticE_cyclic_jet_test
-- name    : ArithmeticE.cyclic_jet_test
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-12T17:35:17.780665+00:00
-- url     : https://prove2.me/theorems/513c60ca-c8ad-4eba-b919-618e27f1e15c
-- title:
--   Choosing algebraic cyclic jets modulo polynomial functional relations
-- statement:
--   Let $f=(f_1,\ldots,f_m)$ be complex formal power series satisfying $Tf'=Bf$, with $T$ and $B$ rational polynomial data. Assume a polynomial relation basis with polynomial left inverse is supplied. Let $\xi\in\mathbb C$ satisfy $T(\xi)\ne0$, and let $a\in\overline{\mathbb Q}^{\,m}$ not be the specialization at $\xi$ of a polynomial relation among the $f_i$.
--
--   There are $n>0$ and algebraic rows $w_0,\ldots,w_{n-1}$, with $w_0=a$, such that every complex polynomial row $P$ satisfying
--
--   $$R_k(P)(\xi)=w_k\qquad(0\le k<n)$$
--
--   gives a polynomial derivative frame of order $n$ for $F=\sum_i P_if_i$ at $\xi$. Here $R_k$ is the cleared derivative-row recurrence. A frame means polynomially independent series $g_j$, a common multiplier $d$, and polynomial coordinates $A,b$ for $dF,\ldots,dF^{(n)}$, with $d(\xi)(\det A)(\xi)\ne0$.
--
--   This separates choosing a basis in the specialized polynomial span from realizing the chosen jets. It does not assert the existence of $P$ or of a minimal scalar equation. Algebraicity of $\xi$ and of the coefficients of $f_i$ is not required in this lemma.
-- source:
--   Auxiliary formalization of Beukers, A refined version of the Siegel–Shidlovskii theorem, Theorem 3.2, printed pp. 6–7 (prescribed derivative rows and determinant equation), https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. These explicit polynomial-numerator and module-coordinate interfaces are derived from the proof, not quoted named lemmas.

import Definitions.Def_clearedDerivativeRows
import Definitions.Def_polynomialDerivativeFrame
open ArithmeticE

theorem ArithmeticE.cyclic_jet_test
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ) * f j)
    (hbasis : RelationBasis f)
    (ξ : ℂ) (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hnot : ¬ ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i : PowerSeries ℂ) * f i = 0) ∧ ∀ i, (p i).eval ξ = a i) :
    ∃ (n : ℕ) (w : ℕ → Fin m → ℂ),
      0 < n ∧
      (∀ k < n, ∀ i, IsAlgebraic ℚ (w k i)) ∧
      (∀ i, w 0 i = a i) ∧
      ∀ P : Fin m → Polynomial ℂ,
        (∀ k < n, ∀ i, (clearedDerivativeRows T B P k i).eval ξ = w k i) →
        PolynomialDerivativeFrame (∑ i, (P i : PowerSeries ℂ) * f i) ξ n := by sorry
