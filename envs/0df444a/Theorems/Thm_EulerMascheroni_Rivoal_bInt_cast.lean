-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_bInt_cast
-- name    : EulerMascheroni.Rivoal.bInt_cast
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:29:00.684502+00:00
-- url     : https://prove2.me/theorems/86ed8a04-9c9b-449f-a2e3-bae64d2de69e
-- title:
--   The integers $b_{n,j}$ are signed $\beta_{n,j}$
-- statement:
--   For $0\le j\le n$,
--   $$
--   b_{n,j}=(-1)^{n-j}\,\beta_{n,j}=(-1)^{n-j}\frac{(3n-j)!}{\big(j!\,(n-j)!\big)^2}
--   $$
--   as rational numbers. In particular $\beta_{n,j}$ is an integer, because $(j!\,(n-j)!)^2$ divides $(3n-j)!$.
--   Here $N_n,D_n,U_{n,j},P_n,b_{n,j}$ are the data of the definition `eulerMascheroni_rivoalPoly` (with $X^{(j)}=X(X-1)\cdots(X-j+1)$), and $\beta_{n,j},h_{n,j},p'_n$ those of `eulerMascheroni_rivoalForms`.
--
--   The divisibility holds since $\beta_{n,j}$ is a multinomial coefficient $\binom{3n-j}{j,\;n-j,\;n-j,\;n}$ times the integer $n!/j!$. The lemma identifies the integer coefficients used in the polynomial definitions with the rational coefficients of Rivoal's forms.
--
--   **Formalization Note** `bInt n j` uses natural-number division, so the statement also records that this division is exact.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); elementary polynomial-side proof: Lemma B1 of the accompanying research notes (Q_CHILD_PROOF.md, section 2).

import Definitions.Def_eulerMascheroni_rivoalPoly

theorem EulerMascheroni.Rivoal.bInt_cast (n j : ℕ) (hj : j ≤ n) :
    (EulerMascheroni.Rivoal.bInt n j : ℚ) = (-1) ^ (n - j) * EulerMascheroni.Rivoal.beta n j := by sorry
