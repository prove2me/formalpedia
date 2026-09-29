-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_partialFraction_value
-- name    : EulerMascheroni.Rivoal.partialFraction_value
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:29:02.430363+00:00
-- url     : https://prove2.me/theorems/e7c9355c-158b-4e3a-86a5-57d78c19ddd2
-- title:
--   Values of $N_n/D_n$ beyond the poles
-- statement:
--   For integers $M>n$,
--   $$
--   \frac{N_n(M)}{D_n(M)}=P_n(M)+\sum_{j=0}^{n}b_{n,j}\,\frac{M^{(j)}}{M-j}.
--   $$
--   Here $N_n,D_n,U_{n,j},P_n,b_{n,j}$ are the data of the definition `eulerMascheroni_rivoalPoly` (with $X^{(j)}=X(X-1)\cdots(X-j+1)$), and $\beta_{n,j},h_{n,j},p'_n$ those of `eulerMascheroni_rivoalForms`.
--
--   This is the partial-fraction identity evaluated at a natural number outside the poles $0,\dots,n$. It rewrites the summand $N_n(M)/(D_n(M)\,M!)$ of the series for Rivoal's remainder $S_n$, so the series splits into pieces that can be summed in closed form.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); elementary polynomial-side proof: Lemma A3 of the accompanying research notes (Q_CHILD_PROOF.md, section 2).

import Definitions.Def_eulerMascheroni_rivoalPoly

theorem EulerMascheroni.Rivoal.partialFraction_value (n M : ℕ) (hM : n < M) :
    (((EulerMascheroni.Rivoal.polyN n).eval (M : ℤ) : ℤ) : ℚ) /
        (((EulerMascheroni.Rivoal.polyD n).eval (M : ℤ) : ℤ) : ℚ) =
      (((EulerMascheroni.Rivoal.polyP n).eval (M : ℤ) : ℤ) : ℚ) +
        ∑ j ∈ Finset.range (n + 1),
          (EulerMascheroni.Rivoal.bInt n j : ℚ) * (M.descFactorial j : ℚ) / ((M : ℚ) - j) := by sorry
