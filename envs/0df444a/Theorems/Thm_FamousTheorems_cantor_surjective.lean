-- Prove2me | Theorems.Thm_FamousTheorems_cantor_surjective
-- name    : FamousTheorems.cantor_surjective
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:55.657985+00:00
-- url     : https://prove2.me/theorems/5271676f-716e-47de-adec-204c09b16ab9
-- title:
--   Cantor's theorem: no surjection onto the power set
-- statement:
--   **No map from a set onto its power set is surjective.**
--
--   For every $f : \alpha \to \mathcal{P}(\alpha)$, $f$ is not surjective — so
--   $|\alpha| < |\mathcal{P}(\alpha)|$ always.
--
--   The diagonal set $D = \{x : x \notin f(x)\}$ is not in the image: if $D = f(y)$ then
--   $y \in D \iff y \notin D$. Two lines, and it applies to every set, finite or infinite.
--
--   The consequence is that there is no largest cardinal — the cardinals form a proper hierarchy —
--   and the same diagonal device reappears in Russell's paradox, Gödel's incompleteness theorems and
--   the undecidability of the halting problem.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cantor_surjective : ∀ {α : Type*} (f : α → Set α), ¬ Function.Surjective f := by sorry

end FamousTheorems
