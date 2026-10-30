-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_lemma_2_a
-- name    : BundleShaping.NoOrderSet.lemma_2_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:15.839011+00:00
-- url     : https://prove2.me/theorems/6974f13e-4064-4968-ae2d-27224ef67c92
-- title:
--   Lemma 2(a), p. 22 — the BTS value function V_t(x) is non-increasing in the net inventory x
-- statement:
--   In the bundle-to-stock model under the standing assumptions, for every period $t=1,\dots,T+1$ the value function $V_t$ of (9) is non-increasing in the net inventory of items: for $x,x'\in\mathbb R^I$,
--
--   $$x\le x'\ \Longrightarrow\ V_t(x')\le V_t(x),$$
--
--   where $\le$ is the coordinatewise order.
--
--   A larger initial inventory only shrinks the feasible set $\{y\ge x\}$ of (9); the monotonicity is used to show that $G_t$ is non-increasing in $y$.
--
--   **Formalization Note.** $V_{T+1}\equiv 0$, so the case $t=T+1$ is included as in the paper.
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 22, Lemma 2(a)

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem lemma_2_a (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T + 1) : Antitone (P.V t) := by sorry

end BundleShaping.NoOrderSet
