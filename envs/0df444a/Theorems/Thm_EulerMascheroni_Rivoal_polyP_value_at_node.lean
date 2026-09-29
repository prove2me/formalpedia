-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_polyP_value_at_node
-- name    : EulerMascheroni.Rivoal.polyP_value_at_node
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:29:05.259642+00:00
-- url     : https://prove2.me/theorems/23fae44e-e638-4b36-9d78-51d279fab0b9
-- title:
--   Regularised values of $P_n$ at the poles
-- statement:
--   For $0\le M\le n$,
--   $$
--   P_n(M)+\sum_{j=0}^{M-1}b_{n,j}\,\frac{M^{(j)}}{M-j}=-M!\,b_{n,M}\,h_{n,M},\qquad h_{n,M}=H_{3n-M}+2H_M-2H_{n-M}.
--   $$
--   Here $N_n,D_n,U_{n,j},P_n,b_{n,j}$ are the data of the definition `eulerMascheroni_rivoalPoly` (with $X^{(j)}=X(X-1)\cdots(X-j+1)$), and $\beta_{n,j},h_{n,j},p'_n$ those of `eulerMascheroni_rivoalForms`.
--
--   The proof differentiates the partial-fraction identity $N_n=P_nD_n+\sum_jb_{n,j}U_{n,j}$ and evaluates at $X=M$, where $D_n(M)=0$. The logarithmic derivatives of the products produce the harmonic numbers. This gives the values of $P_n$ at $0,\dots,n-1$ in terms of Rivoal's coefficients, which is how $p'_n$ arises.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); elementary polynomial-side proof: Lemma A4 of the accompanying research notes (Q_CHILD_PROOF.md, section 2).

import Definitions.Def_eulerMascheroni_rivoalPoly

theorem EulerMascheroni.Rivoal.polyP_value_at_node (n M : ℕ) (hM : M ≤ n) :
    (((EulerMascheroni.Rivoal.polyP n).eval (M : ℤ) : ℤ) : ℚ) +
        ∑ j ∈ Finset.range M,
          (EulerMascheroni.Rivoal.bInt n j : ℚ) * (M.descFactorial j : ℚ) / ((M : ℚ) - j) =
      -(M.factorial : ℚ) * (EulerMascheroni.Rivoal.bInt n M : ℚ) * EulerMascheroni.Rivoal.hcoef n M := by sorry
