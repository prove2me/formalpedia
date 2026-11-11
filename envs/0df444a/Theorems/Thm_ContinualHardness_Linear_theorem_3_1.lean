-- Prove2me | Theorems.Thm_ContinualHardness_Linear_theorem_3_1
-- name    : ContinualHardness.Linear.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:13:05.938462+00:00
-- url     : https://prove2.me/theorems/6269502f-ebe4-4dfa-9cd5-d369c0e27190
-- title:
--   Theorem 3.1 — NP-hard to get accuracy 1/2 + δ on two of T separable symmetric tasks that share a (1 − ε)-accurate linear classifier
-- statement:
--   Let $\varepsilon,\delta>0$ be real and $T>1$ an integer. Consider $T$-tuples of finite symmetric datasets $D_1,\dots,D_T$ with data-points from $\mathbb R^d\times\{-1,1\}$ (rational coordinates and weights, encoded in binary) such that every $D_t$ is linearly separable, i.e. some homogeneous classifier $\operatorname{sign}((r^{(t)})^{\mathsf T}x)$ has $\mathrm{Acc}(D_t,\cdot)=1$. It is NP-hard to distinguish
--   * (**YES**) there is a homogeneous linear classifier $h^*(x)=\operatorname{sign}((r^*)^{\mathsf T}x)$, $r^*\in\mathbb R^d$, with $\mathrm{Acc}(D_t,h^*)\ge1-\varepsilon$ for all $t\in[T]$, from
--   * (**NO**) every linear classifier $h(x)=\operatorname{sign}(r^{\mathsf T}x+c)$, $r\in\mathbb R^d$, $c\in\mathbb R$, satisfies
--   $$\big|\{t\in[T]:\mathrm{Acc}(D_t,h)\ge\tfrac12+\delta\}\big|\le1 .$$
--   Formally, `GapNPHard encodeCL (CLYes ε) (CLNo δ)`: every NP language over a finite nonempty alphabet reduces in polynomial time to codes of instances, members to YES and non-members to NO instances. Consequently, when $\varepsilon+\delta\le\frac12$ (so a YES instance has a classifier with accuracy $\ge\frac12+\delta$ on all $T\ge2$ tasks), no polynomial-time algorithm computes a linear classifier $h$ with $|\{t:\mathrm{Acc}(D_t,h)\ge\frac12+\delta\}|>1$ on all inputs satisfying conditions 1 and 2 unless P = NP; for larger $\varepsilon,\delta$ the search problem only becomes harder. This is the paper's main result: continual learning of even two linearly separable tasks with an unlimited replay buffer is computationally intractable.
--
--   Differences from the source:
--   - generalization: it is NP-hard to compute a linear classifier h with |{t ∈ [T] : Acc(D_t, h) ≥ 1/2 + δ}| > 1, given datasets satisfying conditions 1 and 2 → GapNPHard encodeCL (CLYes ε) (CLNo δ): NP-hard to distinguish valid instances with a common (1 − ε)-accurate homogeneous classifier from valid instances where no linear classifier reaches 1/2 + δ on two tasks; reason: the gap form implies the search form: for ε + δ ≤ 1/2 a solver's output is checked exactly in polynomial time and decides the gap problem, and the search problem for larger ε or δ is at least as hard (the promise grows with ε, the solution set shrinks with δ)
--   - encoding: datasets with data-points from ℝ^d × {−1, 1}, given as input → instances with rational coordinates and rational weights, written in the binary code encodeCL (d is part of the input); the classifiers r*, r, c range over the reals; reason: an input to an algorithm is a finite string; the reduction of Theorem A.8 produces rational data
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 7, Theorem 3.1 (PDF p. 8)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Instance

namespace ContinualHardness.Linear

/-- Theorem 3.1, p. 7 (gap form). For all real `ε, δ > 0` and every integer `T > 1` it is NP-hard
(Karp gap form, over the binary encoding `encodeCL`) to distinguish `T`-tuples of finite symmetric
datasets `D₁, …, D_T` with rational data in `ℝ^d × {−1, 1}`, each separable by a homogeneous
linear classifier, such that
* (YES) some homogeneous linear classifier `sign((r*)ᵀx)` has `Acc(D_t, ·) ≥ 1 − ε` for all `t`,
from such tuples in which
* (NO) every linear classifier `h = sign(rᵀx + c)` has `Acc(D_t, h) ≥ 1/2 + δ` for at most one `t`.
-/
theorem theorem_3_1 (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (T : ℕ) (hT : 1 < T) :
    SetCoverThreshold.SetCover.GapNPHard (encodeCL (T := T)) (CLYes ε) (CLNo δ) := by sorry

end ContinualHardness.Linear
