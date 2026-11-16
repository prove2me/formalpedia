-- Prove2me | Theorems.Thm_BordenaveCollins_Pisier_exists_factorization_of_norm_evalP_lt
-- name    : BordenaveCollins.Pisier.exists_factorization_of_norm_evalP_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:09:11.962117+00:00
-- url     : https://prove2.me/theorems/ecdc0e4c-cd6f-4958-9133-6609aab72137
-- title:
--   Pisier's factorization into linear factors, for unitary letters
-- statement:
--   Let $e$ be a finite family of unitary operators on a Hilbert space that contains the identity and is closed under adjoints (`UnitaryLetters e`). Let $y = \sum_w y_w \otimes w$ be a polynomial in these letters with coefficients $y_w \in M_D(\mathbb C)$, and let $c > \|y(e)\|$, where $y(e) = \sum_w y_w \otimes e(w)$ acts on $D$ copies of the space. Then there are $q \ge 1$, dimensions $D_1 = D, D_2, \dots, D_{q+1} = D$ and matrices $A_{j,l}$ of size $D_j \times D_{j+1}$ such that, with $X_j = \sum_l A_{j,l} \otimes e(l)$,
--   $$y(e) = c\, X_1 X_2 \cdots X_q \qquad\text{and}\qquad \|X_j\| \le 1 \text{ for } 1 \le j \le q.$$
--
--   This is the form of Pisier's linearization theorem (G. Pisier, *On a linearization trick*, Enseign. Math. 64 (2018) 315–326) that Chen, Garza-Vargas, Tropp and van Handel apply in Lemma 9.1 of *A new approach to strong convergence*; there the letters are the left-regular unitaries of the generators of a free group, and here they are arbitrary.
--
--   **Formalization note.** The definitions are in the bundle `Def_BordenaveCollinsFactorization`. The letter type and the Hilbert space are in the lowest universe. No relation among the letters is assumed beyond the three conditions above.
-- source:
--   Pisier, G., On a linearization trick, Enseign. Math. 64 (2018) 315–326, https://doi.org/10.4171/LEM/64-3/4-5, the factorization theorem, for finitely many unitaries closed under adjoints; cited as [59, Theorem 1] and applied in Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), Lemma 9.1, p. 27

import Mathlib
import Definitions.Def_BordenaveCollinsFactorization

namespace BordenaveCollins.Pisier

theorem exists_factorization_of_norm_evalP_lt {ι : Type} [Fintype ι] {L : Type}
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (e : ι → L →L[ℂ] L) (hU : UnitaryLetters e) {D : ℕ}
    (y : List ι →₀ Matrix (Fin D) (Fin D) ℂ) (c : ℝ) (hc : ‖evalP e y‖ < c) :
    ∃ (q : ℕ) (Dim : ℕ → ℕ) (A : ∀ j : ℕ, ι → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)
      (h₁ : Dim 1 = D) (hq : Dim (1 + q) = D),
      1 ≤ q ∧ evalP e y = c • gChainOn e Dim A q h₁ hq ∧
        ∀ j ∈ Finset.Icc 1 q, ‖amp e (A j)‖ ≤ 1 := by
  sorry

end BordenaveCollins.Pisier
