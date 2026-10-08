-- Prove2me | Theorems.Thm_EkelandVP_General_bpLE_upper_closed
-- name    : EkelandVP.General.bpLE_upper_closed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:48:31.427462+00:00
-- url     : https://prove2.me/theorems/eb16007e-a2a3-4d71-9eda-c5f899a4dcfd
-- title:
--   §1, p. 325 — continuity of (1.6): $\{(v,a) \mid (v,a) \succ (v_1,a_1)\}$ is closed in $V \times \mathbb{R}$
-- statement:
--   Let $(V,d)$ be a metric space, $\alpha\in\mathbb{R}$, and $\prec$ the relation (1.6). For every $(v_1,a_1)\in V\times\mathbb{R}$ the set of elements greater than $(v_1,a_1)$,
--
--   $$
--   \{(v,a) \in V\times\mathbb{R} \mid (v_1,a_1) \prec (v,a)\} = \{(v,a) \mid (a-a_1)+\alpha\,d(v_1,v)\le 0\},
--   $$
--
--   is closed in $V\times\mathbb{R}$ with the product topology.
--
--   This is the sense in which Ekeland calls the order continuous; it makes the sets $S_n$ in the proof of Lemma 1.2 closed.
--
--   **Formalization Note** The page fixes $\alpha > 0$ in the sentence that introduces (1.6); closedness holds for every real $\alpha$, so the hypothesis is not needed and not stated.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 325, §1, second sentence after (1.6)

import Mathlib
import Definitions.Def_EkelandVP_General_bpLE

namespace EkelandVP.General

theorem bpLE_upper_closed {V : Type*} [MetricSpace V] (α : ℝ) (p₁ : V × ℝ) :
    IsClosed {p : V × ℝ | bpLE α p₁ p} := by sorry

end EkelandVP.General
