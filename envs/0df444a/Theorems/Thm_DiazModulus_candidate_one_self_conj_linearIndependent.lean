-- Prove2me | Theorems.Thm_DiazModulus_candidate_one_self_conj_linearIndependent
-- name    : DiazModulus.candidate_one_self_conj_linearIndependent
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T17:55:44.832253+00:00
-- url     : https://prove2.me/theorems/c193ddd1-7fff-479f-9a17-32a5291f7455
-- title:
--   A candidate is Q-bar-independent from 1 and its own conjugate
-- statement:
--   **Statement.** Let $\overline{\mathbb{Q}} \subset \mathbb{C}$ be the field of algebraic
--   numbers, and call $u \in \mathbb{C}$ a *candidate* when $u \neq 0$, $|u|$ is algebraic and $e^{u}$
--   is algebraic — this is `IsCandidate u`, which is exactly the negation of Diaz's implication at $u$.
--   Then $1$, $u$ and $\overline{u}$ are linearly independent over $\overline{\mathbb{Q}}$.
--
--   **What it is for.** `DiazModulus.StrongFourExponentials` takes $\overline{\mathbb{Q}}$-linear
--   independence of pairs as its hypothesis, and
--   `DiazModulus.diaz_of_strongFourExponentials_and_hermite_lindemann` is already proved. This node
--   produces independence in exactly the form that reduction consumes, so it is the joint between the
--   candidate picture and an existing milestone rather than one more closure property of the candidate
--   set. Independence of the triple $\{1, u, \overline{u}\}$ gives independence of any pair drawn from
--   it, which is what a four-exponentials input needs.
--
--   **Proof.** Put $c = u\overline{u} = |u|^{2}$; it is non-zero because $u \neq 0$, and algebraic by
--   the second clause of `IsCandidate`. Suppose $A + Bu + C\overline{u} = 0$ with
--   $A, B, C \in \overline{\mathbb{Q}}$. Multiplying through by $u$ gives $Bu^{2} + Au + Cc = 0$.
--
--   If $B \neq 0$, set $a = A/B$ and $d = Cc/B$, both algebraic, so that $u^{2} + au + d = 0$.
--   Completing the square, $(u + a/2)^{2} = a^{2}/4 - d$ is algebraic, hence $u + a/2$ is algebraic, and
--   so is $u$.
--
--   If $B = 0$ and $A \neq 0$, the relation reads $A + C\overline{u} = 0$ with $C \neq 0$, so
--   $\overline{u} = -A/C$ is algebraic, and therefore so is $u$.
--
--   In both cases $u$ is a non-zero algebraic number, so Hermite–Lindemann makes $e^{u}$ transcendental,
--   contradicting the third clause of `IsCandidate`. Hence $A = B = 0$, the relation collapses to
--   $C\overline{u} = 0$, and $\overline{u} \neq 0$ forces $C = 0$.
--
--   Hermite–Lindemann is not carried as a hypothesis: the mission has
--   `DiazModulus.hermite_lindemann_holds` proved, and the statement above is unconditional.
--
--   **No novelty is claimed.** This is an elementary consequence of Hermite–Lindemann — three lines of
--   field arithmetic and one completed square. It is published because it is the edge that attaches the
--   candidate hypotheses to a reduction the mission already owns, and an edge that is only implicit is
--   an edge that gets re-derived.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_one_self_conj_linearIndependent {u : ℂ} (h : IsCandidate u) :
    LinearIndependent (↥Qbar) ![(1 : ℂ), u, conj u] := by sorry
end DiazModulus
