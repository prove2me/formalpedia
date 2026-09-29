-- Prove2me | Theorems.Thm_Diaz_candidate_indistinguishable_by_coeff
-- name    : Diaz.candidate_indistinguishable_by_coeff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T06:44:48.83792+00:00
-- url     : https://prove2.me/theorems/b5ab9d59-dfce-4ba2-9f1f-04155a0aa82c
-- title:
--   No vanishing statement over $\bar{\mathbb{Q}}$ separates a Diaz candidate from an ordinary point of its circle
-- statement:
--   **No vanishing statement with algebraic coefficients distinguishes a candidate from an
--   ordinary point of the same circle.**
--
--   Call $u \in \mathbb{C}$ a **candidate** for Diaz's conjecture when $u \neq 0$, $e^{u}$ is
--   algebraic over $\mathbb{Q}$, and $u\bar u = r^{2}$ for some non-zero real algebraic $r$; then
--   $r = |u|$. Diaz's conjecture is that no candidate exists, and nothing here bears on that.
--
--   The claim is that there exist a point $t$ of the same circle — $t \neq 0$, $t$ transcendental
--   over $\bar{\mathbb{Q}}$, and $t\bar t = r^{2}$ — and a ring homomorphism
--   $\Phi : \mathbb{C} \to \mathbb{C}$ with
--
--   $$\Phi|_{\bar{\mathbb{Q}}} = \mathrm{id}, \qquad \Phi(u) = t, \qquad
--   \Phi(\bar z) = \overline{\Phi(z)} \ \ (z \in \bar{\mathbb{Q}}(u)), \qquad
--   \Phi\bigl(\bar{\mathbb{Q}}(u)\bigr) \subseteq \bar{\mathbb{Q}}(t),$$
--
--   such that for **every** matrix $M$ with entries in $\bar{\mathbb{Q}}(u)$ and all vectors
--   $w$, $v$ with entries in $\bar{\mathbb{Q}}$, the transported matrix $\Phi(M)$ again has entries
--   in $\bar{\mathbb{Q}}(t)$ and
--
--   $$w^{\mathsf T} M v = 0 \quad\Longleftrightarrow\quad w^{\mathsf T} \Phi(M) v = 0 .$$
--
--   Here $\bar{\mathbb{Q}}(u)$ is the smallest subfield of $\mathbb{C}$ containing the algebraic
--   numbers and $u$, written `hull Qbar u`.
--
--   **Reading.** The four clauses pinning $\Phi$ down are what makes the last one say something.
--   A ring homomorphism of $\mathbb{C}$ fixing $\bar{\mathbb{Q}}$ and sending $u$ to $t$ is
--   determined on $\bar{\mathbb{Q}}(u)$ (`Diaz.eqOn_hull`), so an entry of $\Phi(M)$ *is* the
--   expression defining the corresponding entry of $M$, read with $t$ in place of $u$ —
--   conjugations included, since $\Phi$ intertwines conjugation there. So the two sides of the
--   equivalence are literally the same vanishing statement, evaluated at the candidate and at the
--   ordinary point. No such statement can separate them.
--
--   **Proof.** From `Diaz.candidate_indistinguishable` one gets $t$ and $\Phi$ with the first three
--   clauses. That $\Phi$ maps $\bar{\mathbb{Q}}(u)$ into $\bar{\mathbb{Q}}(t)$ is a closure
--   argument: $\Phi^{-1}\bigl(\bar{\mathbb{Q}}(t)\bigr)$ is a subfield of $\mathbb{C}$ containing
--   $\bar{\mathbb{Q}}$ and $u$, and $\bar{\mathbb{Q}}(u)$ is the smallest such. That
--   $t\bar t = r^{2}$ comes from applying $\Phi$ to $u\bar u = r^{2}$: the right side is algebraic
--   and so fixed, and the left side goes to $\Phi(u)\Phi(\bar u) = t\,\bar t$ by the intertwining.
--   The equivalence is `Diaz.coeff_transfer_iff`, applied to this $\Phi$ with
--   $K = \bar{\mathbb{Q}}$.
--
--   **Relation to what is already on the platform.**
--   `Diaz.candidate_no_vanishing_coeff_Qbar` is the *specialised* case: one specific $2 \times 2$
--   matrix, $H = \begin{pmatrix} u & r \\ r & \bar u\end{pmatrix}$, with $\mathrm{Fin}\,2$
--   coefficient vectors, and a non-vanishing conclusion. `Diaz.coeff_transfer` is the forward
--   identity for coefficients. This node is the statement those two were specialisations and
--   fragments of, and is Theorem 5.1 of the companion note cited below.
--   Note also that $t\bar t = r^{2}$ is stated in the note's Theorem 5.1 but absent from the platform
--   node `Diaz.candidate_indistinguishable`; it is recovered here, and without it the statement
--   could not say "the same circle".
--
--   **What is deliberately not claimed.** Nothing about $e^{t}$. If $e^{t}$ were algebraic then $t$
--   would itself be a candidate, so asserting its transcendence would be asserting an instance of
--   the conjecture. And nothing here advances or retreats from Diaz's conjecture; it constrains the
--   *methods* that could settle it.
--
--   **Attribution.** The mathematics is Carlo Perassi's: the statement is Theorem 5.1 of his companion note to
--   https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). No novelty is
--   claimed for it; the contribution is the formalisation.
-- source:
--   Carlo Perassi, note accompanying https://github.com/carlok/diaz-modulus-lean (version 1.8, 24 September 2026, GitHub release note-v1.8), Theorem 5.1

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.candidate_indistinguishable_by_coeff
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ Qbar) (hrr : conj r = r) (hr0 : r ≠ 0)
    (h : u * conj u = r ^ 2) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥Qbar) t ∧ t * conj t = r ^ 2 ∧
      ∃ Φ : ℂ →+* ℂ, (∀ a ∈ Qbar, Φ a = a) ∧ Φ u = t ∧
        (∀ z ∈ hull Qbar u, Φ (conj z) = conj (Φ z)) ∧
        (∀ z ∈ hull Qbar u, Φ z ∈ hull Qbar t) ∧
        ∀ (p q : ℕ) (M : Matrix (Fin p) (Fin q) ℂ) (w : Fin p → ℂ) (v : Fin q → ℂ),
          (∀ i j, M i j ∈ hull Qbar u) → (∀ i, w i ∈ Qbar) → (∀ j, v j ∈ Qbar) →
            (∀ i j, Φ (M i j) ∈ hull Qbar t) ∧
              ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔
                (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by sorry
