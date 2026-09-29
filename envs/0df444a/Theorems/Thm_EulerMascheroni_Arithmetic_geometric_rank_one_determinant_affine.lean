-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_geometric_rank_one_determinant_affine
-- name    : EulerMascheroni.Arithmetic.geometric_rank_one_determinant_affine
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T19:51:24.064404+00:00
-- url     : https://prove2.me/theorems/2bf5b790-00f1-4716-8816-46a4a0e1971b
-- title:
--   Geometric rank-one dependence makes a determinant affine in its parameter
-- statement:
--   Let $R$ be a commutative ring, $A$ an $(n+1)\times(n+1)$ matrix over $R$, and $r\in R$. There exist $a,b\in R$, independent of $t$, such that
--   $$\det\bigl(A_{ij}+r^{i+j}t\bigr)=at+b\qquad(t\in R).$$
--   Subtracting $r^i$ times the first row from row $i>0$ removes the parameter from every row except the first; multilinearity then gives the assertion.
--
--   This is an obstruction to a naive higher-degree Hankel strategy for the Euler–Gompertz constant. Raw factorial remainders have the form $m_k(t)=(-1)^k(t-S_k)$, where $S_k=\sum_{j<k}(-1)^j j!$. Their Hankel matrices have precisely the displayed form with $r=-1$, so increasing the determinant size still produces an affine expression in $t$. The theorem does not rule out Hankel determinants of differently normalized or transformed Padé errors.
-- source:
--   Elementary determinant row operations. Application prompted by Matala-aho and Zudilin, Euler factorial series and global relations, https://arxiv.org/html/1703.02633, Section 4; no novelty is claimed for the rank-one determinant identity.

import Mathlib

theorem EulerMascheroni.Arithmetic.geometric_rank_one_determinant_affine {R : Type*} [CommRing R] (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (r : R) :
    ∃ a b : R, ∀ t : R,
      Matrix.det (fun i j => A i j + r^(i.val+j.val)*t) = a*t+b := by sorry
