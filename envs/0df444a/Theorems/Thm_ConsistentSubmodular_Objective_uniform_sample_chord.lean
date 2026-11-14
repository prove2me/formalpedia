-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_uniform_sample_chord
-- name    : ConsistentSubmodular.Objective.uniform_sample_chord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:23.539599+00:00
-- url     : https://prove2.me/theorems/8b41dd70-1423-42bf-a129-8d05bd5897dd
-- title:
--   Uniform independent thinning dominates the all-or-nothing mixture
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$, let $A,B\subseteq[n]$ and $p\in[0,1]$. Let $S$ be the random subset of $A$ containing each element of $A$ independently with probability $p$. Then
--
--   $$(1-p)\,f(B)+p\,f(B\cup A)\;\le\;\sum_{S\subseteq A}p^{|S|}(1-p)^{|A\setminus S|}\,f(B\cup S)\;=\;\mathbb{E}\big[f(B\cup S)\big].$$
--
--   In words, independent uniform thinning of the core $A$ is at least as valuable as the all-or-nothing mixture that takes $A$ entirely with probability $p$ and nothing otherwise, for an arbitrary contracted buffer $B$.
--
--   This chord bound is a submodular concavity estimate used to compare randomized sampling of a core with the mixtures $H_j(p)$ of the window analysis.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/SamplingOperators.lean#L172-L199 (`ConsistentSubmodular.Objective.uniform_sample_chord`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.uniform_sample_chord (A B : Finset (Fin n)) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1 - p) * f.value B + p * f.value (B ∪ A) ≤ sampleAdd A (fun _ => p) f.value B := by sorry
