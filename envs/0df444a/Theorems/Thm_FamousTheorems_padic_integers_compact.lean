-- Prove2me | Theorems.Thm_FamousTheorems_padic_integers_compact
-- name    : FamousTheorems.padic_integers_compact
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:22.3479+00:00
-- url     : https://prove2.me/theorems/494f9fe9-e283-4871-ae78-6d5b01828c68
-- title:
--   Compactness of the p-adic integers
-- statement:
--   **Compactness of the $p$-adic integers.** For every prime $p$, the ring $\mathbb Z_p$ of $p$-adic integers is a compact topological space.
--
--   Compactness of $\mathbb Z_p$ makes $\mathbb Q_p$ locally compact, so it carries a Haar measure. This is the foundation of $p$-adic integration and of the adelic methods of Tate's thesis.
--
--   **Formalization note.** Mathlib's instance `PadicInt.compactSpace`. `PadicInt p` is Mathlib's $\mathbb Z_p$, written `ℤ_[p]` in Mathlib notation.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PadicInt.compactSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem padic_integers_compact (p : ℕ) [Fact p.Prime] : CompactSpace (PadicInt p) := by sorry

end FamousTheorems
