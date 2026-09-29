-- Prove2me | Theorems.Thm_CannonFloydParry_exists_standardDyadicPartition_of_isThompson
-- name    : CannonFloydParry.exists_standardDyadicPartition_of_isThompson
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-16T12:33:49.834372+00:00
-- url     : https://prove2.me/theorems/31bee44b-79a2-492d-9e09-4a8736a1bba3
-- title:
--   Every element of $F$ is given by a pair of standard dyadic partitions
-- statement:
--   A **standard dyadic interval** is an interval of the form
--   $$\left[\frac{a}{2^{k}},\ \frac{a+1}{2^{k}}\right], \qquad a, k \in \mathbb{N},$$
--   and a **standard dyadic partition** of $[0,1]$ is a partition $0 = x_0 < x_1 < \cdots < x_n = 1$ all of whose intervals $[x_{i}, x_{i+1}]$ are standard dyadic intervals — equivalently, one obtained from $\{[0,1]\}$ by repeatedly halving an interval.
--
--   The assertion is the normal-form lemma of the source's section 2. Let $f$ be an order isomorphism of $[0,1]$ satisfying the piecewise-linearity condition `IsThompson`: finitely many breakpoints, all dyadic, and every slope an integer power of two. Then there are standard dyadic partitions
--   $$0 = x_0 < x_1 < \cdots < x_n = 1, \qquad 0 = y_0 < y_1 < \cdots < y_n = 1$$
--   with the **same** number of intervals such that $f$ carries $[x_{i}, x_{i+1}]$ affinely onto $[y_{i}, y_{i+1}]$ for every $i$; explicitly, for $x_{i} \le z \le x_{i+1}$,
--   $$f(z) = \frac{y_{i+1} - y_{i}}{x_{i+1} - x_{i}}\,\bigl(z - x_{i}\bigr) + y_{i}.$$
--
--   This is exactly the statement that $f$ is described by a *tree diagram*: the two partitions are the leaf sets of the domain and range trees. The mechanism is that the breakpoints of $f$ are dyadic and its slopes are powers of two, so one may refine the partition cut out by the breakpoints — halving intervals on both sides — until every piece is a standard dyadic interval whose image under $f$ is again a standard dyadic interval. Refining a standard dyadic partition by halving keeps it standard, and refining the domain side forces a matching refinement of the range side, which is why the two partitions can be arranged to have equally many intervals.
--
--   Note that a pairing of two *arbitrary* dyadic partitions with equally many intervals does not in general arise from an element of $F$: the affine map between two dyadic intervals has power-of-two slope only when both are standard dyadic, which is why the standardness hypothesis cannot be dropped.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Section 2 (tree diagrams), Lemma 2.2 and Theorem 2.5, pp. 220-224 (supporting steps for Corollary 2.6, that $A$ and $B$ generate $F$)

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_standardDyadicPartition_of_isThompson {f : UI ≃o UI} (hf : IsThompson f) :
    ∃ (n : ℕ) (x y : Fin (n + 1) → UI),
      StrictMono x ∧ StrictMono y ∧
      (x 0 : ℝ) = 0 ∧ (x (Fin.last n) : ℝ) = 1 ∧
      (y 0 : ℝ) = 0 ∧ (y (Fin.last n) : ℝ) = 1 ∧
      (∀ i : Fin n, ∃ a k : ℕ,
        (x i.castSucc : ℝ) = a / 2 ^ k ∧ (x i.succ : ℝ) = (a + 1) / 2 ^ k) ∧
      (∀ i : Fin n, ∃ a k : ℕ,
        (y i.castSucc : ℝ) = a / 2 ^ k ∧ (y i.succ : ℝ) = (a + 1) / 2 ^ k) ∧
      (∀ (i : Fin n) (z : UI), (x i.castSucc : ℝ) ≤ (z : ℝ) → (z : ℝ) ≤ (x i.succ : ℝ) →
        (f z : ℝ) =
          ((y i.succ : ℝ) - (y i.castSucc : ℝ)) / ((x i.succ : ℝ) - (x i.castSucc : ℝ))
            * ((z : ℝ) - (x i.castSucc : ℝ)) + (y i.castSucc : ℝ)) := by
  sorry

end CannonFloydParry
