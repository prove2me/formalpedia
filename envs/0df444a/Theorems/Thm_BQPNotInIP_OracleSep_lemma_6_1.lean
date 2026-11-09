-- Prove2me | Theorems.Thm_BQPNotInIP_OracleSep_lemma_6_1
-- name    : BQPNotInIP.OracleSep.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:49.636482+00:00
-- url     : https://prove2.me/theorems/2b607cab-1465-475f-8aaa-0bf7c70bfa33
-- title:
--   Lemma 6.1 — softmax smoothing with global derivative bounds
-- statement:
--   Let $C:\mathbb R^m\to\mathbb R$ be a $(d,L)$-AM circuit and let $\lambda>0$. There exists a globally smooth convex function $F:\mathbb R^m\to\mathbb R$ for which, at every real vector $x$,
--   $$
--   0\le F(x)-C(x)\le\frac{dL\ln2}{\lambda},\qquad
--   \|\nabla F(x)\|_1\le L,\qquad
--   \|\nabla^2F(x)\|_1\le2\lambda dL^2.
--   $$
--   Smooth means $C^\infty$. Both derivative norms are the entrywise sums of absolute coordinate derivatives, and their bounds hold on the entire space. This provides the smooth convex test functions needed by the Gaussian comparison results.
--
--   Differences from the source:
--   - encoding: real vectors, smooth functions, Gaussian expectations and suprema of derivative norms → coordinates indexed by Fin m, C∞ expressed as ContDiff ℝ (⊤ : ℕ∞), entrywise sums of coordinate derivatives, and pointwise bounds on the stated domains; reason: these are the same finite-dimensional objects and avoid default-valued real suprema
-- source:
--   Adam Bouland, Andrew Huang, Anand Natarajan, Itay Shalit, Avishay Tal, BQP ⊆ IP Does Not Relativize, STOC 2027 submission #156 (October 2026), Lemma 6.1, PDF p. 13 (printed p. 11). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/156.pdf#page=13

import Definitions.Def_BQPNotInIP_OracleSep_AMCircuits
import Definitions.Def_BQPNotInIP_OracleSep_Analysis

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BQPNotInIP.OracleSep

theorem lemma_6_1 {m d L : ℕ} (C : AMCircuit m d L)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ F : RVec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ ConvexOn ℝ Set.univ F ∧
      (∀ x, 0 ≤ F x - C.eval x ∧ F x - C.eval x ≤ (d:ℝ)*L*Real.log 2/lam) ∧
      (∀ x, gradientL1 F x ≤ L) ∧
      (∀ x, hessianL1 F x ≤ 2*lam*d*(L:ℝ)^2) := by sorry

end BQPNotInIP.OracleSep
