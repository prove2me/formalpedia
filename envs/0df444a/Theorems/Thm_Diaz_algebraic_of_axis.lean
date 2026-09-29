-- Prove2me | Theorems.Thm_Diaz_algebraic_of_axis
-- name    : Diaz.algebraic_of_axis
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:59:24.715718+00:00
-- url     : https://prove2.me/theorems/b2f3b1a6-8393-4b94-8f71-c9b5a45a192d
-- title:
--   On either axis, an algebraic modulus forces the point itself to be algebraic
-- statement:
--   **Source.** The statement — if
--   $u \in \mathbb{R} \cup i\mathbb{R}$ and $|u| \in \overline{\mathbb{Q}}$, then
--   $u \in \overline{\mathbb{Q}}$ — is known: it is the first step of Case 1 of the proof of Proposition 1 of G. Diaz, *Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle*, J. Théor. Nombres Bordeaux 16 (2004), 535–553, p. 551, and it plays the same role in Remark 2.2 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). This node is its formalisation. No novelty is claimed; the statement is elementary.
--
--   **Statement.** Let $u \in \mathbb{C}$ lie on one of the two axes, that is $\bar u = u$ ($u$ real)
--   or $\bar u = -u$ ($u$ purely imaginary). If $|u|$ is algebraic over $\mathbb{Q}$, then so is $u$.
--
--   **Proof.** On either axis $u^{2} = \pm\, u \bar u = \pm |u|^{2}$, so $u^{2}$ is algebraic, and a
--   complex number whose square is algebraic is algebraic.
--
--   **What this is not.** The axis reduction asserts more: that the candidate locus $\mathcal{D}$ is *disjoint*
--   from $\mathbb{R} \cup i\mathbb{R}$. Getting there from the statement above needs one further input,
--   Hermite–Lindemann — for $u \neq 0$ algebraic, $e^{u}$ is transcendental — which is not available in
--   the platform's Mathlib at this revision (only the analytic half,
--   `NumberTheory.Transcendental.Lindemann.AnalyticalPart`, is present). The full axis reduction,
--   conditional on that input, is already on this mission as
--   `DiazModulus.diaz_on_axes_of_hermite_lindemann`. What is published here is the half of the argument
--   that is unconditional, and it is the half that carries the elementary content: on an axis, an
--   algebraic modulus pins the point itself down to $\overline{\mathbb{Q}}$.
-- source:
--   Known: the first step of Case 1 of the proof of Proposition 1 in G. Diaz, Utilisation de la conjugaison complexe dans l'étude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Théor. Nombres Bordeaux 16 (2004), 535–553, p. 551. It plays the same role in Remark 2.2 of Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.10, 27 September 2026 (GitHub release note-v1.10). Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.algebraic_of_axis {u : ℂ} (hax : conj u = u ∨ conj u = -u)
    (h : IsAlgebraic ℚ ‖u‖) : IsAlgebraic ℚ u := by sorry
