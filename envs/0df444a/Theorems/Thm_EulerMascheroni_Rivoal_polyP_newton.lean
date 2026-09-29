-- Prove2me | Theorems.Thm_EulerMascheroni_Rivoal_polyP_newton
-- name    : EulerMascheroni.Rivoal.polyP_newton
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T21:29:04.266362+00:00
-- url     : https://prove2.me/theorems/ad26c690-7acd-4076-9470-f9e8541c4178
-- title:
--   Newton coordinates of $P_n$ and the constant $p'_n$
-- statement:
--   For every $n\ge1$ there are integers $a_0,\dots,a_{n-1}$ with
--   $$
--   P_n=\sum_{j=0}^{n-1}a_j\,X^{(j)}\quad\text{in }\mathbb Z[X],\qquad\text{hence}\quad P_n(M)=\sum_{j=0}^{n-1}a_j\,M^{(j)}\ \ (M\in\mathbb N),
--   $$
--   and
--   $$
--   \sum_{j=0}^{n-1}(-1)^j a_j=(-1)^{n+1}\,p'_n .
--   $$
--   Here $N_n,D_n,U_{n,j},P_n,b_{n,j}$ are the data of the definition `eulerMascheroni_rivoalPoly` (with $X^{(j)}=X(X-1)\cdots(X-j+1)$), and $\beta_{n,j},h_{n,j},p'_n$ those of `eulerMascheroni_rivoalForms`.
--
--   $P_n$ has integer coefficients and degree at most $n-1$, and the monic falling factorials $X^{(j)}$ form a $\mathbb Z$-basis of $\mathbb Z[X]$. The second identity combines the node values of $P_n$ with the finite identity $\sum_{k=0}^{s}(-1)^kE_{s-k}/k!=1$, where $E_s=\sum_{l\le s}1/l!$. Since $\sum_{M\ge0}(-1)^MM^{(j)}/M!=(-1)^je^{-1}$, it gives $\sum_{M\ge0}(-1)^MP_n(M)/M!=(-1)^{n+1}p'_n/e$. It also shows that $p'_n$ is an integer.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4, at z=-1 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); elementary polynomial-side proof: Lemma A1+A5 of the accompanying research notes (Q_CHILD_PROOF.md, section 2).

import Definitions.Def_eulerMascheroni_rivoalPoly

theorem EulerMascheroni.Rivoal.polyP_newton (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : ℕ → ℤ,
      EulerMascheroni.Rivoal.polyP n =
          ∑ j ∈ Finset.range n, Polynomial.C (a j) * descPochhammer ℤ j ∧
      (∀ M : ℕ, (((EulerMascheroni.Rivoal.polyP n).eval (M : ℤ) : ℤ) : ℚ) =
          ∑ j ∈ Finset.range n, (a j : ℚ) * (M.descFactorial j : ℚ)) ∧
      ((∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * a j : ℤ) : ℚ) =
          (-1) ^ (n + 1) * EulerMascheroni.Rivoal.pCoef n := by sorry
