-- Prove2me | Theorems.Thm_Diaz_exists_transcendental_on_circle
-- name    : Diaz.exists_transcendental_on_circle
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:24.396559+00:00
-- url     : https://prove2.me/theorems/83d7590f-ae1f-41f8-a2e1-62ec6b6dfd49
-- title:
--   Every circle over an algebraic base carries a transcendental point, with an explicit witness
-- statement:
--   Let $L \subseteq \mathbb{C}$ be a subfield that is algebraic over $\mathbb{Q}$, and let $r \in \mathbb{C}$ be non-zero with $r \in L$ and $\bar r \in L$. Then there is $t \in \mathbb{C}$ with
--
--   $$t \neq 0, \qquad t \ \text{transcendental over } L, \qquad t\,\bar t = r\,\bar r, \qquad t\,\bar t \in L.$$
--
--   **The witness is explicit:** $t = r\,e^{\,i}$. It is transcendental over $L$ because $e^{i}$ is (by Hermite–Lindemann, $i$ being algebraic and non-zero) and $r \in L$ is invertible there; and $e^{i}\,\overline{e^{i}} = e^{i}e^{-i} = 1$, so $t\bar t = r\bar r$ exactly.
--
--   **Both conclusions are needed.** The model lemmas consume the *membership* $t\bar t \in L$, while the transfer results consume the *equality* $t\bar t = r\bar r$. An earlier version of the source project gave only the membership, with the consequence that no exhibited $t$ could discharge the transfer hypotheses.
--
--   **The hypothesis $\bar r \in L$ is not redundant.** It does not follow from $r \in L$: for $L = \mathbb{Q}(2^{1/3}\omega)$ and $r = 2^{1/3}\omega$ one has $r\bar r = 2^{2/3} \notin L$. Every result that consumes this theorem already assumes $L$ conjugation-stable, so nothing is lost.
--
--   **Role.** The model results take a transcendental point on the circle as a hypothesis. This theorem shows the hypothesis is not vacuous, and does so constructively rather than by a cardinality argument — the point that is algebraically indistinguishable from a Diaz candidate is an ordinary, nameable complex number.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Model.lean#L165-L214

import Mathlib

open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

theorem Diaz.exists_transcendental_on_circle {L : Subfield ℂ}
    [Algebra.IsAlgebraic ℚ (↥L)] {r : ℂ} (hr : r ∈ L) (hrc : conj r ∈ L)
    (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥L) t ∧ t * conj t = r * conj r
      ∧ t * conj t ∈ L := by sorry
