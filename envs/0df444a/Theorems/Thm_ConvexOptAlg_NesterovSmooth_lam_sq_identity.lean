-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_lam_sq_identity
-- name    : ConvexOptAlg.NesterovSmooth.lam_sq_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:01.337329+00:00
-- url     : https://prove2.me/theorems/0a7de21a-6734-4725-bfb0-8f5dd268baa9
-- title:
--   Proof of Theorem 3.19, p. 294 — the step sequence satisfies λ²_{s−1} = λ²_s − λ_s
-- statement:
--   Let $\lambda_0=0$ and $\lambda_t=\frac{1+\sqrt{1+4\lambda_{t-1}^2}}2$ for $t\ge1$. Then for every $s\ge1$,
--
--   $$\lambda_{s-1}^2=\lambda_s^2-\lambda_s.$$
--
--   The book uses this identity "by definition" to turn the one-step inequality into a telescoping one.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, p. 294 ("using that by definition λ²_{s−1} = λ²_s − λ_s")

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- The identity `λ_{s−1}² = λ_s² − λ_s` used in the proof of Theorem 3.19 (Bubeck,
arXiv:1405.4980v2, p. 294, "by definition"), for every `s ≥ 1`. -/
theorem lam_sq_identity (s : ℕ) (hs : 1 ≤ s) :
    lam (s - 1) ^ 2 = lam s ^ 2 - lam s := by sorry

end ConvexOptAlg.NesterovSmooth
