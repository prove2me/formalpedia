-- Prove2me | Theorems.Thm_Diaz_exists_transcendental_on_circle_Qbar
-- name    : Diaz.exists_transcendental_on_circle_Qbar
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:37.932775+00:00
-- url     : https://prove2.me/theorems/d5fd3edc-e2b3-4ce8-81fe-0031219b2b44
-- title:
--   Every algebraic circle carries a point transcendental over $\bar{\mathbb{Q}}$
-- statement:
--   Let $r \in \bar{\mathbb{Q}}$ be non-zero. Then there exists $t \in \mathbb{C}$ with
--
--   $$t \neq 0, \qquad t \ \text{transcendental over } \bar{\mathbb{Q}}, \qquad t\,\bar t = r\,\bar r, \qquad t\,\bar t \in \bar{\mathbb{Q}} .$$
--
--   **Why.** This is `Diaz.exists_transcendental_on_circle` instantiated at $L = \bar{\mathbb{Q}}$. Two side conditions have to be met and both are supplied here: $\bar{\mathbb{Q}}$ is algebraic over $\mathbb{Q}$ (the named instance in the definition bundle, which does not fire on its own through the `IntermediateField → Subfield` coercion), and $\bar{\mathbb{Q}}$ is stable under complex conjugation — if $p \in \mathbb{Q}[X]$ kills $a$ then it kills $\bar a$, its coefficients being rational and hence fixed by conjugation. The witness remains explicit: $t = r\,e^{\,i}$.
--
--   **Role.** The model results take a transcendental point of the circle as a hypothesis. Over the intended base — the algebraic numbers — this theorem discharges that hypothesis. Combined with the closure theorem it is what allows a hypothetical Diaz counterexample to be *paired* with an ordinary complex number of the same modulus, which is the shape of the negative result.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Instantiation.lean#L68-L73

import Mathlib
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.exists_transcendental_on_circle_Qbar {r : ℂ} (hr : r ∈ Qbar) (hr0 : r ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥Qbar) t ∧ t * conj t = r * conj r
      ∧ t * conj t ∈ Qbar := by sorry
