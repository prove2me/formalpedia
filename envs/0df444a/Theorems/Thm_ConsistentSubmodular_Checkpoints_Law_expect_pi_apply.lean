-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_Law_expect_pi_apply
-- name    : ConsistentSubmodular.Checkpoints.Law.expect_pi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:17.268361+00:00
-- url     : https://prove2.me/theorems/ad6d9af1-4f58-44f7-9cda-43a9c48129f5
-- title:
--   Marginal of one coordinate of a product law
-- statement:
--   Let $\iota$ and $X$ be finite types, with $\iota$ having decidable equality, and let $(\mu_i)_{i\in\iota}$ be finite probability laws on $X$. Let $\mu=\bigotimes_i\mu_i$ be the product law on $\iota\to X$, with weight $\prod_i\mu_i(x_i)$. Then for every coordinate $i$ and every $F:X\to\mathbb R$
--   $$\mathbb E_{x\sim\mu}\big[F(x_i)\big]\;=\;\mathbb E_{y\sim\mu_i}\big[F(y)\big].$$
--
--   This marginal property of independent coordinates is used in the checkpoint reduction when computing expectations that depend on a single independently drawn component.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointLaw.lean#L86-L104 (`ConsistentSubmodular.Checkpoints.Law.expect_pi_apply`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointLaw

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
open ConsistentSubmodular.Checkpoints.Law
variable {Ω : Type*} [Fintype Ω]

theorem ConsistentSubmodular.Checkpoints.Law.expect_pi_apply {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (μ : ι → Law X) (i : ι) (F : X → ℝ) :
    (pi μ).expect (fun x => F (x i)) = (μ i).expect F := by sorry
