-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_3_11
-- name    : AsymSpecConn.Supplement.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:22:19.709403+00:00
-- url     : https://prove2.me/theorems/8c97cd58-c183-4b3c-b522-c2a95752d790
-- title:
--   Theorem 3.11 — $\Gamma$ consists of star centers of the basic joint spectrum
-- statement:
--   Let $b_1=\langle2,1,1\rangle$, $b_2=\langle1,2,1\rangle$, and $b_3=\langle1,1,2\rangle$ be the three basic complex matrix-multiplication tensors, and let
--
--   $$
--   \Gamma=\operatorname{conv}\{(1,1,0),(0,1,1),(1,0,1)\}.
--   $$
--
--   Then $\Gamma\subseteq\log\Delta(b_1,b_2,b_3)$, and $\log\Delta(b_1,b_2,b_3)$ is star-convex with respect to every point of $\Gamma$.
--
--   This identifies an explicit two-dimensional family of centers inside the logarithmic joint spectrum.
--
--   Differences from the source: none.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 3.11, p.27

import Mathlib
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_Supplement_logValueSet
import Definitions.Def_AsymSpecConn_Supplement_basicMM

set_option autoImplicit false

namespace AsymSpecConn.Supplement

/-- **Theorem 3.11** (p.27) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): `Gamma` is contained in the coordinatewise base-two logarithm of the
joint spectrum of `⟨2,1,1⟩`, `⟨1,2,1⟩`, `⟨1,1,2⟩`, and every point of `Gamma` is a star center.

**Formalization Note** Source legs 1,2,3 are `Fin 3` indices 0,1,2. The logarithm is base 2. -/
theorem theorem_3_11 :
    gamma3 ⊆ logValueSet (AsymSpecConn.tensorPreorder ℂ (by norm_num)) (basicMM ℂ) ∧
    StarConvexWith (logValueSet (AsymSpecConn.tensorPreorder ℂ (by norm_num)) (basicMM ℂ))
      gamma3 := by sorry

end AsymSpecConn.Supplement
