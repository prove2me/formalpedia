-- Prove2me | Theorems.Thm_DiazModulus_kronecker_factorisation
-- name    : DiazModulus.kronecker_factorisation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-19T18:41:16.805028+00:00
-- url     : https://prove2.me/theorems/0760fd27-195c-4419-b38c-ebbcfe9f9db0
-- title:
--   The interpolation matrix of a candidate's exponential system is a Kronecker product, with non-zero determinant
-- statement:
--   **The interpolation matrix of the natural exponential system splits.**
--
--   Let $u$ be a candidate: $u \neq 0$, with $|u|$ and $\mathrm{e}^{u}$ both algebraic. Put
--   $\alpha = \mathrm{e}^{u}$ and, for $0 \le a, b, m, n \le N$, let
--   $E_{a,b}(z,w) = \exp(a u z + b \overline{u} w)$. Arrange the values $E_{a,b}(m,n)$ as a matrix $M$
--   whose rows are indexed by the pairs $(a,b)$ and whose columns are indexed by the pairs $(m,n)$.
--   Then
--
--   $$M = A \otimes B, \qquad A = (\alpha^{am}), \quad B = (\overline{\alpha}^{\,bn}),$$
--
--   the Kronecker product; its determinant is $(\det A)^{N+1}(\det B)^{N+1}$; and it is non-zero.
--
--   **What it means.** Each factor is a Vandermonde matrix — $A$ in the nodes $\alpha^{a}$, $B$ in the
--   nodes $\overline{\alpha}^{\,b}$ — and those nodes are pairwise distinct because
--   $|\alpha| = \mathrm{e}^{\operatorname{Re} u} \neq 1$. So the interpolation determinant attached to
--   the two-variable exponential system of a candidate factors into two independent one-variable
--   determinants, and the arithmetic of the candidate, the relation $u \overline{u} = \rho$, does not
--   appear in it. A Schwarz lemma for Cartesian products asks for vanishing on a full simplex of
--   derivatives, so one is thrown back on the values, and the values see nothing.
--
--   **Role.** One of the two obstructions to running a classical interpolation argument on a
--   candidate. The other is that no first-order arithmetic differential operator exists
--   (`DiazModulus.no_first_order_arithmetic_operator`): the arithmetic enters only through
--   $\partial_z \partial_w$, which is not a derivation.
--
--   **Honesty about its shape.** The hypothesis class is conjecturally empty. Diaz's conjecture asserts
--   that no candidate exists, so this is a statement about a hypothetical counterexample, as is the
--   rest of the obstruction line of this mission. Nothing here asserts that a candidate exists.
--
--   **Hypotheses.** `hre : u.re ≠ 0` is not an extra assumption in substance: for a candidate the real
--   part is transcendental, which is `DiazModulus.candidate_re_transcendental` (Proved), granting
--   Hermite-Lindemann (Proved on this mission). The candidate hypothesis `hu` is carried so that the
--   statement reads as Proposition 5.10 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9); **the proof never uses it**, and the factorisation
--   holds for every $u$ with $\operatorname{Re} u \neq 0$. The matrices $M$, $A$, $B$ are given by their
--   entries rather than by a definition, so no new Definition node is needed.
--
--   **Not formalised here.** The note adds that neither $\rho$ nor the relation
--   $u \overline{u} = \rho$ occurs in $\det M$. That is a remark about the shape of an expression, not a
--   proposition about its value, and it is not part of the formal statement.
--
--   **Novelty.** Kronecker and Vandermonde determinants of Cartesian exponential systems
--   are standard. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 5.10. Background: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000 (the Schneider-Lang criterion and Schwarz' lemma for Cartesian products); G. Diaz, J. Theor. Nombres Bordeaux 19 (2007), 373-391.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem kronecker_factorisation
    (u : ℂ) (hu : IsCandidate u) (hre : u.re ≠ 0) (N : ℕ)
    (M : Matrix (Fin (N + 1) × Fin (N + 1)) (Fin (N + 1) × Fin (N + 1)) ℂ)
    (hM : ∀ p q, M p q =
      Complex.exp (u * ((p.1 : ℕ) * (q.1 : ℕ)) + conj u * ((p.2 : ℕ) * (q.2 : ℕ))))
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hA : ∀ a m, A a m = (Complex.exp u ^ (a : ℕ)) ^ (m : ℕ))
    (hB : ∀ b n, B b n = (conj (Complex.exp u) ^ (b : ℕ)) ^ (n : ℕ)) :
    M = Matrix.kroneckerMap (· * ·) A B ∧
      M.det = A.det ^ (N + 1) * B.det ^ (N + 1) ∧ M.det ≠ 0 := by sorry

end DiazModulus
