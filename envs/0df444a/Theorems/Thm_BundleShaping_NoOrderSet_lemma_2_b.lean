-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_lemma_2_b
-- name    : BundleShaping.NoOrderSet.lemma_2_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:14.952441+00:00
-- url     : https://prove2.me/theorems/fbdda145-c171-4970-b1da-9a5442990993
-- title:
--   Lemma 2(b), p. 22 — G_t(y, z, q) is non-increasing in the order-up-to level y for given (z, q)
-- statement:
--   In the bundle-to-stock model under the standing assumptions, for every period $1\le t\le T$, every scheduled production vector $z\in\mathbb R^J$ and every market-share vector $q\in\Omega$, the function
--
--   $$y\ \longmapsto\ G_t(y,z,q)=G^m_t(y,z,q)+\beta E\,V_{t+1}(y-Ad_t)$$
--
--   is non-increasing on $\mathbb R^I$ for the coordinatewise order.
--
--   Raising the order-up-to level beyond what the assembly plan needs only adds procurement and holding cost; this is what makes a no-order set possible.
--
--   **Formalization Note.** The paper says "for all $t=1,\dots,T+1$", but $G_t$ is defined only for $t\le T$ (it involves $V_{t+1}$), so the statement is for $1\le t\le T$. The vector $q$ ranges over $\Omega$, the domain of the decision.
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 22, Lemma 2(b)

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem lemma_2_b (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (z q : J → ℝ) (hq : q ∈ P.Ω) : Antitone (fun y : I → ℝ => P.G t y z q) := by sorry

end BundleShaping.NoOrderSet
