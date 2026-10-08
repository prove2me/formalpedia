-- Prove2me | Theorems.Thm_BregmanPPA_EqMult_theorem6_ppa_run
-- name    : BregmanPPA.EqMult.theorem6_ppa_run
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:21.504977+00:00
-- url     : https://prove2.me/theorems/170f98f6-a003-4cc1-a469-db255e7b63be
-- title:
--   Proof of Theorem 6 — the multipliers $p^k$ of (9) are a Bregman proximal point run on $\partial(-d)$
-- statement:
--   Consider problem (7) under its standing assumptions: $X \subseteq \mathbb R^n$ closed and convex, $f : \mathbb R^n \to (-\infty,+\infty]$ convex and lower semicontinuous, $\inf\{f(x)\mid x \in X\} < \infty$, and the dual functional $d(p) = \inf_{x\in X}\{f(x) + \langle p, Ax - b\rangle\}$ not identically $-\infty$. Let $h$ be a Bregman function with zone $\mathbb R^m$ and $\operatorname{im}(\nabla h) = \mathbb R^m$, let $c_k > 0$, and let $\{(x^k,p^k)\}$ conform to recursion (9),
--   $$x^{k+1} \in \operatorname*{arg\,min}_{x\in X}\Bigl\{ f(x) + \tfrac{1}{c_k} h^*\bigl(\nabla h(p^k) + c_k(Ax - b)\bigr)\Bigr\},\qquad p^{k+1} = \nabla h^*\bigl(\nabla h(p^k) + c_k(Ax^{k+1} - b)\bigr).$$
--   Then the multiplier sequence conforms to the Bregman proximal point recursion for $\partial(-d)$:
--   $$p^{k+1} = \bigl(\nabla h + c_k\, \partial(-d)\bigr)^{-1}\bigl(\nabla h(p^k)\bigr)\qquad\text{for all } k,$$
--   that is, $\frac{1}{c_k}\bigl(\nabla h(p^k) - \nabla h(p^{k+1})\bigr) \in \partial(-d)(p^{k+1})$ for every $k$.
--
--   This identity reduces the convergence of the nonquadratic method of multipliers to Theorem 1 applied to the maximal monotone operator $\partial(-d)$.
--
--   **Formalization Note** The recursion is encoded in form (4), as in the definition of runs; the zone is all of $\mathbb R^m$, so the condition $p^k \in S$ is automatic. $\partial(-d)$ is the subdifferential of the `EReal` function $p \mapsto -d(p)$. $\operatorname{im}\nabla h = \mathbb R^m$ is surjectivity of $\nabla h$. The paper states this claim in the proof of Theorem 6, under the standing assumptions of §4.1, which are all hypotheses here.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 213, proof of Theorem 6 (from "We show that the sequence {p^k} produced by (9) conforms to the Bregman nonlinear proximal point formula" to "Thus, p^{k+1} = (∇h + c_k∂(−d))^{-1}(∇h(p^k)), as claimed.")

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_fenchelConjugate
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_EqMult_EqConstrainedProgram

open InertialFB.IFB ConvexOptimization Filter Topology

namespace BregmanPPA.EqMult
theorem theorem6_ppa_run {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hP : IsEqProgram X f) (hd : ∃ p, dualEq A b X f p ≠ ⊥)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) :
    BregmanPPA.Convergence.IsBregmanPPARun Set.univ h (BregmanPPA.Convergence.subdiffOp (negDual A b X f)) c p := by sorry
end BregmanPPA.EqMult
