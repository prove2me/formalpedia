-- Prove2me | Theorems.Thm_ChatterjeeQFT_hermOfVec_det_bijection
-- name    : ChatterjeeQFT.hermOfVec_det_bijection
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:36:12.342595+00:00
-- url     : https://prove2.me/theorems/2aef12eb-530d-4035-aaf0-af72b2c39aa5
-- title:
--   $\det M(x) = (x,x)$ and $M$ is a bijection onto the Hermitian $2\times2$ matrices
-- statement:
--   The map
--
--   $$M(x) \;=\; \begin{pmatrix} x^0 + x^3 & x^1 - ix^2 \\ x^1 + ix^2 & x^0 - x^3\end{pmatrix}$$
--
--   carries $\mathbb{R}^{1,3}$ bijectively onto the space of $2\times2$ complex Hermitian matrices,
--   and its determinant is the Minkowski square:
--
--   $$\det M(x) \;=\; (x,x) \;=\; (x^0)^2 - (x^1)^2 - (x^2)^2 - (x^3)^2 .$$
--
--   Bijectivity is expressed through the explicit inverse map $H \mapsto \operatorname{vec}(H)$:
--   $\operatorname{vec}(M(x)) = x$ for every four-vector $x$, and $M(\operatorname{vec}(H)) = H$ for
--   every Hermitian $H$. These are the two facts of §25.2 on which the covering map $\kappa$ rests:
--   the determinant identity is what makes $\kappa(A)$ a Lorentz transformation for
--   $A \in SL(2,\mathbb{C})$.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 §25.2, pp. 107-108 ("the above definition provides a bijection between $\mathbb{R}^{1,3}$ and the space of $2\times2$ complex Hermitian matrices. Moreover, $\det M(x) = (x,x)$").

import Mathlib
import Definitions.Def_ChatterjeeQFT_SL2C
open Matrix
open scoped ComplexOrder

namespace ChatterjeeQFT

theorem hermOfVec_det_bijection :
    (∀ x : Fin 4 → ℝ, (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ)) ∧
      (∀ x : Fin 4 → ℝ, vecOfHerm (hermOfVec x) = x) ∧
      (∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → hermOfVec (vecOfHerm H) = H) := by sorry

end ChatterjeeQFT
