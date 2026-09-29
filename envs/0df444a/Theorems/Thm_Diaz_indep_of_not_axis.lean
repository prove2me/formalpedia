-- Prove2me | Theorems.Thm_Diaz_indep_of_not_axis
-- name    : Diaz.indep_of_not_axis
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:59:23.527694+00:00
-- url     : https://prove2.me/theorems/d0122243-8084-4b12-8d8c-dda4a03b6bb1
-- title:
--   Off both axes, a point and its conjugate are $\mathbb{Q}$-linearly independent
-- statement:
--   **Source.** The statement — if $u \in \mathcal{L}\setminus(\mathbb{R} \cup i\mathbb{R})$, then $u$ and $\bar u$ are linearly
--   independent over $\mathbb{Q}$ — is known: G. Diaz states it in the proof of Théorème 3 of *Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle*, J. Théor. Nombres Bordeaux 16 (2004), 535–553, p. 539, and again in Case 2 of the proof of his Proposition 1, p. 551. It is also the first step of the proof of Theorem 6.1 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). This node is its formalisation; no novelty is claimed, and the
--   statement is elementary.
--
--   **Statement.** Let $u \in \mathbb{C}$ be off both axes: $\bar u \neq u$ and $\bar u \neq -u$. Then
--   for rational $a, b$, the relation $a u + b \bar u = 0$ forces $a = b = 0$.
--
--   **Two remarks on the form.** First, the hypothesis $u \in \mathcal{L}$ of the source is not
--   used — the argument is purely geometric — so it is dropped here, and the node applies to any
--   complex number off the axes, a candidate or not. Second, the axis condition is written with
--   conjugation rather than with real and imaginary parts: $\bar u = u$ says $u$ is real, $\bar u = -u$
--   says $u$ is purely imaginary, and the case $u = 0$ is excluded automatically since $\bar 0 = 0$.
--
--   **Proof.** Conjugating the relation gives $a \bar u + b u = 0$, since $a$ and $b$ are rational.
--   Eliminating $\bar u$ between the two relations gives $(a^{2} - b^{2}) u = 0$, and $u \neq 0$, so
--   $a = \pm b$. If $a = b$ then $a(u + \bar u) = 0$, so either $a = 0$ — and then $b = 0$ — or
--   $\bar u = -u$, excluded. If $a = -b$ then $a(u - \bar u) = 0$, so either $a = 0$ — and then
--   $b = 0$ — or $\bar u = u$, excluded. (Another proof runs through
--   $u/\bar u \in \mathbb{Q}$ having modulus one, hence being $\pm 1$; the elimination above is the
--   same argument without the division.)
--
--   **Relation to what is already published.** `Diaz.indep` and `Diaz.indep_three` give independence
--   from transcendence of $u$ over the base field. This node gives it from a hypothesis that is purely
--   about position in the plane, which is what is used to reduce Diaz's problem to points off
--   the axes.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.indep_of_not_axis {u : ℂ} (h1 : conj u ≠ u) (h2 : conj u ≠ -u)
    {a b : ℚ} (h : (a : ℂ) * u + (b : ℂ) * conj u = 0) : a = 0 ∧ b = 0 := by sorry
