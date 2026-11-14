-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_expect_run_ge
-- name    : ConsistentSubmodular.Checkpoints.expect_run_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:12.312206+00:00
-- url     : https://prove2.me/theorems/a29ec438-58b6-4897-85c1-8431aad79e1d
-- title:
--   Expected value of Algorithm 1 at time $u+1$ against every small competitor
-- statement:
--   Let $0\le\alpha\le1$ and assume that every instance of the clairvoyant addition-robust problem with one arrival per stage admits an $\alpha$-addition-robust distribution. Let $f$ be a nonnegative monotone submodular objective, $P=(\ell,\kappa,h,s)$ parameters valid for the budget $k$, $u\in\mathbb N$ with $u+1\le n$, and $T\subseteq X_{u+1}$ with $|T|\le\kappa$. Draw the random choices as follows: the checkpoint sample $A_i$ of block $i$ is drawn from the $\alpha$-addition-robust distribution for the checkpoint instance at time $i\ell$ with budget $\kappa$, independently over $i$, and the subblocks $\sigma_i$ are drawn independently and uniformly from $\{0,\dots,h-1\}$. Then
--   $$\Bigl(1-\frac1h\Bigr)\,\alpha\, f(T)\;\le\;\mathbb E\bigl[f(\mathrm{ALG}_{u+1})\bigr],$$
--   where $\mathrm{ALG}_{u+1}$ is the set held by Algorithm 1 at time $u+1$.
--
--   Before the selected subblock the algorithm holds the old core together with the current arrivals, and after it the new core together with them. In either case the addition-robust guarantee of the corresponding checkpoint gives $\alpha f(T)$ in expectation, and the selected subblock is independent of the checkpoint samples. This is the approximation part of the proof of Lemma 1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/Checkpoints.lean#L218-L347 (`ConsistentSubmodular.Checkpoints.expect_run_ge`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_Checkpoints

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ} {α : ℝ}

theorem ConsistentSubmodular.Checkpoints.expect_run_ge (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hadm : AdmitsAdditionRobust α)
    (f : Objective n) {P : Params} {k : ℕ} (hP : P.Valid k) (u : ℕ) (hu : u + 1 ≤ n)
    {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (u + 1)) (hTcard : T.card ≤ P.κ) :
    (1 - 1 / (P.h : ℝ)) * (α * f.value T) ≤
      (sampleLaw hadm f P hP.subblocks_pos).expect
        (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u + 1))) := by sorry
