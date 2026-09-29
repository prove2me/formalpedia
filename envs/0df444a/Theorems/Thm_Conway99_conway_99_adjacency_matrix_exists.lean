-- Prove2me | Theorems.Thm_Conway99_conway_99_adjacency_matrix_exists
-- name    : Conway99.conway_99_adjacency_matrix_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-11T19:40:04.898422+00:00
-- url     : https://prove2.me/theorems/c4d343fc-712e-432f-9820-bdb95039c39d
-- title:
--   Adjacency-matrix form of Conway's 99-graph problem: $A^2+A=12I+2J$
-- statement:
--   Conway's 99-graph problem asks for a strongly regular graph with parameters $(99,14,1,2)$. This statement is the adjacency-matrix form of that existence question.
--
--   The assertion is that there exists a $99\times 99$ matrix $A=(a_{ij})$ with natural number entries such that
--
--   1. $a_{ij}\in\{0,1\}$ for all $i,j$;
--   2. $a_{ij}=a_{ji}$ for all $i,j$;
--   3. $a_{ii}=0$ for all $i$;
--   4. for all $i,j$,
--   $$
--   (A^{2})_{ij}+a_{ij}=12\,[i=j]+2,
--   $$
--   that is, $A^{2}+A=12I+2J$ with $I$ the identity matrix and $J$ the all-ones matrix.
--
--   A symmetric $0/1$ matrix with zero diagonal is exactly the adjacency matrix of a simple graph $G$ on $99$ vertices, and $(A^{2})_{ij}$ counts the common neighbours of $i$ and $j$. On the diagonal, condition 4 reads $(A^{2})_{ii}=14$, which is the degree of vertex $i$, so $G$ is $14$-regular. Off the diagonal it splits into two cases: if $i$ and $j$ are adjacent then $a_{ij}=1$ and $(A^{2})_{ij}=1$, so adjacent vertices have exactly one common neighbour; if they are distinct and non-adjacent then $a_{ij}=0$ and $(A^{2})_{ij}=2$, so non-adjacent vertices have exactly two common neighbours. The four conditions therefore hold for some $A$ if and only if a strongly regular graph with parameters $(99,14,1,2)$ exists.
--
--   The formulation is the specialisation to $(n,k,\lambda,\mu)=(99,14,1,2)$ of the standard identity $A^{2}=kI+\lambda A+\mu (J-I-A)$ characterising strongly regular graphs. It states the problem as a finite arithmetic condition on a $0/1$ matrix, the form in which computational searches and orbit-matrix arguments operate.
--
--   **Formalization Note** Entries are natural numbers with the constraint $a_{ij}\in\{0,1\}$ imposed explicitly, and the matrix square is written entrywise as $\sum_k a_{ik}a_{kj}$; the right-hand side uses `if i = j then 12 else 0` for the term $12\,[i=j]$.
-- source:
--   J. H. Conway, 'Five $1,000 Problems (Update 2017)', OEIS, https://oeis.org/A248380/a248380.pdf (Problem 1); adjacency-matrix reformulation via the strongly regular graph identity A^2 = kI + lambda*A + mu*(J - I - A) with (n,k,lambda,mu) = (99,14,1,2), see A. E. Brouwer and W. H. Haemers, 'Spectra of Graphs', Springer 2012, Section 9.1, p. 115.

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Conway99

theorem conway_99_adjacency_matrix_exists :
    ∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j = (if i = j then 12 else 0) + 2) := by sorry

end Conway99
