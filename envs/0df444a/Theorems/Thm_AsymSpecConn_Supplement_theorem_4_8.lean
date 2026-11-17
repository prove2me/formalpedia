-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_4_8
-- name    : AsymSpecConn.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:27:14.351385+00:00
-- url     : https://prove2.me/theorems/563dad69-6632-497d-813b-900d84b18e84
-- title:
--   Theorem 4.8 — arbitrary-field star-convexity for the three basic tensors
-- statement:
--   Let $K$ be an arbitrary field. For the three basic matrix-multiplication tensors $b_1=\langle2,1,1\rangle$, $b_2=\langle1,2,1\rangle$, and $b_3=\langle1,1,2\rangle$, the set
--
--   $$
--   \log\Delta_K(b_1,b_2,b_3)
--   $$
--
--   is star-convex with respect to every point of $\Gamma=\operatorname{conv}\{(1,1,0),(0,1,1),(1,0,1)\}$.
--
--   The conclusion is uniform over all fields, without a characteristic-zero or algebraic-closure assumption.
--
--   Differences from the source: none.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 4.8, p.35

import Mathlib
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_Supplement_logValueSet
import Definitions.Def_AsymSpecConn_Supplement_basicMM

set_option autoImplicit false

namespace AsymSpecConn.Supplement

universe u

/-- **Theorem 4.8** (p.35) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): over every field, the logarithmic joint spectrum of the three basic
matrix-multiplication tensors is star-convex with respect to every point of `Gamma`.

**Formalization Note** `K` is an arbitrary Lean field; no characteristic-zero, perfectness, or
algebraic-closure hypothesis is present. -/
theorem theorem_4_8 (K : Type u) [Field K] :
    StarConvexWith
      (logValueSet (AsymSpecConn.tensorPreorder K (by norm_num)) (basicMM K)) gamma3 := by sorry

end AsymSpecConn.Supplement
