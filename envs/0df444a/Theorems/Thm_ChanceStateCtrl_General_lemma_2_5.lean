-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_lemma_2_5
-- name    : ChanceStateCtrl.General.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:41.41599+00:00
-- url     : https://prove2.me/theorems/fde72f58-c7ac-47dc-9395-db2e1ff1e89c
-- title:
--   Lemma 2.5, p. 7 — for jointly quasi-convex g, (9) is the convex problem (20) with φ̃ = −log φ + log p convex and lsc
-- statement:
--   Assume Assumption 2.1 ($U$ a reflexive separable Banach space, $\xi\sim\mathcal N(0,\Sigma)$ nondegenerate, $g$ locally Lipschitzian and convex in its second argument), let $g$ in addition be quasi-convex jointly in both variables, and let $p\in(0,1]$. Define the extended-valued function
--   $$
--   \tilde\varphi(u)=-\log\varphi(u)+\log p\qquad(u\in U),\qquad -\log0:=+\infty .
--   $$
--   Then:
--
--   1. $\varphi(u)\ge p$ if and only if $\tilde\varphi(u)\le0$, for every $u\in U$; hence (9) is equivalent to the problem $\min_{u\in U}\{F(u)\mid\tilde\varphi(u)\le0\}$ of (20);
--   2. $\tilde\varphi$ takes values in $\mathbb R\cup\{+\infty\}$;
--   3. $\tilde\varphi$ is convex;
--   4. $\tilde\varphi$ is lower semicontinuous.
--
--   This convex reformulation is what turns the nonconvex problem (9) into one where classical convex optimality conditions apply.
--
--   **Formalization Note** Convexity of the extended-valued $\tilde\varphi$ is convexity of its epigraph. Part 1 is the paper's "(9) and (20) are equivalent optimization problems" (same objective, same feasible set).
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 7, Lemma 2.5

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem lemma_2_5 {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_qc : QuasiconvexOn ℝ Set.univ (Function.uncurry g)) (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ u : U, p ≤ probFn P ξ g u ↔ phiTilde P ξ g p u ≤ 0) ∧
      (∀ u : U, phiTilde P ξ g p u ≠ ⊥) ∧
      ConvexEpi (phiTilde P ξ g p) ∧
      LowerSemicontinuous (phiTilde P ξ g p) := by sorry

end ChanceStateCtrl.General
