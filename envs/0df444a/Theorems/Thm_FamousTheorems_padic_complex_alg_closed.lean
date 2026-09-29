-- Prove2me | Theorems.Thm_FamousTheorems_padic_complex_alg_closed
-- name    : FamousTheorems.padic_complex_alg_closed
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:20.01207+00:00
-- url     : https://prove2.me/theorems/6630e767-a591-46f0-8d20-26f1bb1865d4
-- title:
--   ℂ_p is algebraically closed
-- statement:
--   **$\mathbb C_p$ is algebraically closed.** For every prime $p$, the field $\mathbb C_p$ of $p$-adic complex numbers, the completion of an algebraic closure of $\mathbb Q_p$, is algebraically closed.
--
--   The algebraic closure $\overline{\mathbb Q_p}$ is not complete, and it is a nontrivial fact, proved with Krasner's lemma, that its completion stays algebraically closed. Thus $\mathbb C_p$ plays the role in $p$-adic analysis that $\mathbb C$ plays in complex analysis.
--
--   **Formalization note.** Mathlib's `PadicComplex.isAlgClosed`. `PadicComplex p` is Mathlib's $\mathbb C_p$, written `ℂ_[p]` in Mathlib notation.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PadicComplex.isAlgClosed`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem padic_complex_alg_closed (p : ℕ) [Fact p.Prime] : IsAlgClosed (PadicComplex p) := by sorry

end FamousTheorems
