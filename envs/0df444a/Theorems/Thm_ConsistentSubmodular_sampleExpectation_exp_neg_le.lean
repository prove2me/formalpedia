-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_exp_neg_le
-- name    : ConsistentSubmodular.sampleExpectation_exp_neg_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:21.955421+00:00
-- url     : https://prove2.me/theorems/b4523ce7-cf00-412a-922e-4debd26b5f4e
-- title:
--   Exponential moment of a monotone submodular function with marginals at most one
-- statement:
--   Let $U$ be a finite set, $p:U\to[0,1]$, and let $S\subseteq U$ be a random subset containing each $i\in U$ independently with probability $p_i$; write $\mathbb E$ for this expectation. Let $G$ be a real function on finite sets that is monotone ($A\subseteq B\Rightarrow G(A)\le G(B)$), submodular ($G(A\cup B)+G(A\cap B)\le G(A)+G(B)$), and has marginals at most one: $G(A\cup\{e\})-G(A)\le 1$ for all $A$ and $e$. Then for every real $\lambda$,
--
--   $$\mathbb E\big[e^{-\lambda G(S)}\big]\;\le\;\exp\!\Big(-\lambda\,G(\emptyset)+\big(\mathbb E[G(S)]-G(\emptyset)\big)\big(e^{-\lambda}-1\big)\Big).$$
--
--   This is the analogue, for monotone submodular functions with marginals at most one, of the exponential moment of a sum of independent indicators with the same mean. It is the basis of the lower-tail bound for submodular functions.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ExponentialTails.lean#L111-L201 (`ConsistentSubmodular.sampleExpectation_exp_neg_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_exp_neg_le (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    (hcap : ∀ A e, G (insert e A) - G A ≤ 1) (lam : ℝ) :
    sampleExpectation U p (fun S => Real.exp (-lam * G S)) ≤
      Real.exp (-lam * G ∅ + (sampleExpectation U p G - G ∅) * (Real.exp (-lam) - 1)) := by sorry
