-- Prove2me | Theorems.Thm_BudgetFeasSubmod_Main_lemma_3_7
-- name    : BudgetFeasSubmod.Main.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:01.653236+00:00
-- url     : https://prove2.me/theorems/1b19d536-a4ce-4983-8825-da35c7bee2c7
-- title:
--   Lemma 3.7, p. 12 — if v(T) ≥ k·max v(i), a uniform random halving of T keeps ≥ (k−1)/(4k)·v(T) on both sides w.p. ≥ 1/2
-- statement:
--   Let $v$ be a normalized non-negative submodular function on a finite set $A$, $T\subseteq A$, and $k$ a positive integer with
--   $$
--   v(T)\ge k\cdot\max_{i\in T}v(i).
--   $$
--   Divide $T$ uniformly at random into $T_1$ and $T_2=T\setminus T_1$ (each element independently to either side with probability $1/2$). Then with probability at least $1/2$,
--   $$
--   v(T_1)\ge\frac{k-1}{4k}\,v(T)\quad\text{and}\quad v(T_2)\ge\frac{k-1}{4k}\,v(T).
--   $$
--
--   The paper attributes this to Bei et al. and Leonardi et al.; it is what guarantees that both halves of the random partition in Sample-then-Greedy retain a constant fraction of the optimum.
--
--   **Formalization Note** The probability is a count over the $2^{|T|}$ equally likely subsets $T_1\subseteq T$: "probability $\ge1/2$" is $2^{|T|}\le 2\cdot\#\{\text{good }T_1\}$. The hypothesis $v(T)\ge k\max_{i\in T}v(i)$ is written $k\,v(\{i\})\le v(T)$ for every $i\in T$. The standing assumptions of §2 (normalized, non-negative) are included.
-- source:
--   Amanatidis, Kleer & Schäfer, Budget-Feasible Mechanism Design for Non-Monotone Submodular Objectives: Offline and Online, arXiv:1905.00848v2, p. 12, Lemma 3.7

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

namespace BudgetFeasSubmod.Main

open Finset

/-- Lemma 3.7, p. 12: if `v(T) ≥ k · max_{i ∈ T} v(i)`, then for a uniformly random split of `T`
into `T₁` and `T₂ = T ∖ T₁`, with probability at least `1/2` both halves have value at least
`((k − 1)/(4k)) v(T)`. The probability is a count over the `2^{|T|}` subsets `T₁ ⊆ T`. -/
theorem lemma_3_7 {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ) (T : Finset A)
    (k : ℕ) (hv : IsValuation v) (hk : 0 < k) (hT : ∀ i ∈ T, (k : ℝ) * v {i} ≤ v T) :
    2 ^ T.card ≤ 2 * (T.powerset.filter (fun T₁ =>
      ((k : ℝ) - 1) / (4 * k) * v T ≤ v T₁ ∧ ((k : ℝ) - 1) / (4 * k) * v T ≤ v (T \ T₁))).card := by sorry

end BudgetFeasSubmod.Main
