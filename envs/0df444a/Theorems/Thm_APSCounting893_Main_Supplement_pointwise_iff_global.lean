-- Prove2me | Theorems.Thm_APSCounting893_Main_Supplement_pointwise_iff_global
-- name    : APSCounting893.Main.Supplement.pointwise_iff_global
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:11:11.016187+00:00
-- url     : https://prove2.me/theorems/1d3759c0-725c-4f83-813c-e03e888684b0
-- title:
--   Theorem 7.3 — Pointwise and global annihilator certificates
-- statement:
--   Fix arbitrary complex polynomials $f,f_1,\ldots,f_m$ in $n$ variables and put $\Phi=(f_1,\ldots,f_m,u,1-uf)$ with $u$ independent. Write $\operatorname{Ann}(\Phi)$ for the polynomial substitution kernel. The following are equivalent:
--
--   $$\forall c\in\mathbb C^m\ \exists Q_c\in\operatorname{Ann}(\Phi): Q_c(c,0,0)=1,$$
--   $$\exists Q\in\operatorname{Ann}(\Phi): Q(Y_1,\ldots,Y_m,0,0)=1\text{ identically}.$$
--
--   The left side ranges over every point, and the right side is a single polynomial identity on the whole slice. This is the local-to-global certificate result for integral closure.
--
--   Differences from the source:
--   - encoding: Y1,...,Ym,U,V → Y indexed by Fin m, with U,V indexed by Fin 2 in a disjoint sum; reason: canonical reindexing into the published complex annihilator preserves its exact substitution kernel
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 7.3, p. 28

import Definitions.Def_APSCounting893_Main_Supplement_Certificates

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Theorem 7.3: the entire Y-slice is identically one, not just its value at zero. -/
theorem pointwise_iff_global (n m : ℕ) (F : PolynomialMap ℂ n m)
    (f : Polynomials ℂ n) :
    (∀ c : Affine ℂ m, ∃ Q : Certificate ℂ m,
      certificateAnnihilates F f Q ∧ certificateAt c Q = 1) ↔
    (∃ Q : Certificate ℂ m, certificateAnnihilates F f Q ∧ certificateSlice Q = 1) := by sorry

end APSCounting893.Main.Supplement
