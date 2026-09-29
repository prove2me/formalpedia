-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_polyN_eq_partialFraction
-- name    : EulerMascheroni.Rivoal.polyN_eq_partialFraction
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:29:02.220696+00:00
-- url     : https://prove2.me/theorems/8a9e73bd-a03d-4bb6-b262-69feb86afb58
-- title:
--   Partial-fraction identity $N_n=P_nD_n+\sum_j b_{n,j}U_{n,j}$
-- statement:
--   For every $n\ge0$, in $\mathbb Z[X]$,
--   $$
--   N_n=P_n\,D_n+\sum_{j=0}^{n}b_{n,j}\,U_{n,j},\qquad U_{n,j}=X^{(j)}\prod_{\substack{0\le i\le n\\ i\ne j}}(X-i).
--   $$
--   Here $N_n,D_n,U_{n,j},P_n,b_{n,j}$ are the data of the definition `eulerMascheroni_rivoalPoly` (with $X^{(j)}=X(X-1)\cdots(X-j+1)$), and $\beta_{n,j},h_{n,j},p'_n$ those of `eulerMascheroni_rivoalForms`.
--
--   Equivalently, $N_n/D_n=P_n+\sum_j b_{n,j}X^{(j)}/(X-j)$ as rational functions. The proof shows that $N_n-\sum_j b_{n,j}U_{n,j}$ vanishes at $0,1,\dots,n$, using $N_n(M)=b_{n,M}\,M!\,\prod_{i\ne M}(M-i)$. Hence it is divisible by $D_n=\prod_{i=0}^n(X-i)$, and the division defining $P_n$ is exact.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); elementary polynomial-side proof: Lemma A0-A3 of the accompanying research notes (Q_CHILD_PROOF.md, section 2).

import Definitions.Def_eulerMascheroni_rivoalPoly

theorem EulerMascheroni.Rivoal.polyN_eq_partialFraction (n : ℕ) :
    EulerMascheroni.Rivoal.polyN n =
      EulerMascheroni.Rivoal.polyP n * EulerMascheroni.Rivoal.polyD n +
        ∑ j ∈ Finset.range (n + 1),
          Polynomial.C (EulerMascheroni.Rivoal.bInt n j) * EulerMascheroni.Rivoal.polyU n j := by sorry
