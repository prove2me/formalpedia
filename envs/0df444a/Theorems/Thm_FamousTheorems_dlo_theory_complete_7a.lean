-- Prove2me | Theorems.Thm_FamousTheorems_dlo_theory_complete_7a
-- name    : FamousTheorems.dlo_theory_complete_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:29.275559+00:00
-- url     : https://prove2.me/theorems/fa8661bb-9e16-4b39-bc30-fb431969dda9
-- title:
--   The theory of dense linear orders without endpoints is complete
-- statement:
--   **The theory of dense linear orders without endpoints is complete.** The first-order theory DLO of dense linear orders without endpoints, in the language with one binary relation $\le$, is complete: for every sentence $\sigma$, either DLO $\vdash\sigma$ or DLO $\vdash\neg\sigma$.
--
--   The proof uses Cantor's back-and-forth theorem that all countable models are isomorphic to $(\mathbb Q,\le)$, together with the Łoś–Vaught test. It follows that $(\mathbb Q,\le)$ and $(\mathbb R,\le)$ satisfy the same first-order sentences, and that DLO is decidable. It is a standard first example of an $\aleph_0$-categorical theory.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.dlo_isComplete`. `Language.order.dlo` is the theory of dense linear orders without endpoints in the language of orders. `Theory.IsComplete` means that the theory is satisfiable and that every sentence or its negation is a semantic consequence of it.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.dlo_isComplete`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dlo_theory_complete_7a : FirstOrder.Language.order.dlo.IsComplete := by sorry

end FamousTheorems
