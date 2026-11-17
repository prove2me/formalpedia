-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_7_3
-- name    : AvoidPlast.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:55:31.293457+00:00
-- url     : https://prove2.me/theorems/756e55b4-c58f-4e83-807b-f1eeeadb1b49
-- title:
--   Theorem 7.3 — the low-space analogue of Theorem 7.2
-- statement:
--   Let $S(n)\ge\log n$, $m(n)\le k(n)=m(n)\cdot2^{j(n)}<n$ and $\ell=m-\log(k/m)-1>0$. Let $C[\ell\to k]$ be a $\mathrm{SPACE}(S(n))$-evaluable indexed family such that $\mathrm{Avoid}_C\notin\mathrm{SearchNP}$, and let $\mathcal D$ be the class of co-non-deterministic machines running in simultaneous time $2^{O(S(n))}$ and space $O(S(n)+\ell(n))$ and using $m(n)$ bits of randomness. Then there is no SearchNP-computable targeted $(1/2)$-HSG against $\mathcal D$ that on $n$-bit inputs has seed length $\log(k/m)$ and output length $m$.
--
--   The paper omits the proof as essentially the same as that of Theorem 7.2.
--
--   Differences from the source:
--   - reading: $m(n)\le k(n)<n$, $\ell>0$ → required for every sufficiently large $n$; reason: at $n=0$ the constraint $k(n)<n$ is unsatisfiable, so "for every $n$" would make the theorem vacuous
--   - reading: $\mathrm{Avoid}_C\in\mathrm{SearchNP}$ → a non-deterministic polynomial-time machine solves $\mathrm{Avoid}_C$ on every input of every sufficiently large length; reason: solutions need not exist for short inputs, where the constraints fail; as in Theorem 6.1
--   - reading: co-non-deterministic machines of space $O(S+\ell)$ → the co-non-deterministic choices are read once (one-way tape); the random string is read-only; reason: the usual convention for space-bounded non-determinism; the term $\ell$ in the space bound is the cost of storing the guessed input
--   - encoding: time $2^{O(S(n))}$, space $O(S(n)+\ell(n))$ → time $\lceil2^{K(S(n)+1)}\rceil$, work space $K(S(n)+\ell(n)+1)$, co-non-deterministic choices of length at most the time bound; reason: reading R2
--   - encoding: $S(n)\ge\log n$; $k/m$ a power of two → $\log_2 n\le S(n)$; $k=m\cdot2^j$; reason: the same parameters
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.3, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_SolvesAvoidNDB
import Definitions.Def_AvoidPlast_Supplement_coNDAccepts
import Definitions.Def_AvoidPlast_Supplement_IsSearchNPGen
import Definitions.Def_AvoidPlast_Supplement_HitsTargeted
import Definitions.Def_AvoidPlast_Supplement_OneWayTape

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 7.3 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.40), the low-space analogue of Theorem 7.2. Let `S(n) ≥ log n`,
`m(n) ≤ k(n) = m(n)·2^{j(n)} < n` and `ℓ = m - j - 1 > 0`, and let `C[ℓ → k]` be a
`SPACE(S(n))`-evaluable indexed family with `Avoid_C ∉ SearchNP`. Let `D` be the class of
co-non-deterministic machines running in simultaneous time `2^{O(S(n))}` and space `O(S(n) + ℓ(n))`
and using `m(n)` random bits. Then there is no SearchNP-computable targeted `(1/2)`-HSG against `D`
that on `n`-bit inputs has seed length `j` and output length `m`.

**Formalization Note** The co-non-deterministic choices are read once (`OneWayTape`), the usual
convention for space-bounded non-determinism; the random string is read-only. `Avoid_C ∈ SearchNP`
is solvability on every input of every sufficiently large length, as in Theorem 6.1. -/
theorem theorem_7_3 (S : ℕ → ℝ) (hS : ∀ n : ℕ, Real.logb 2 n ≤ S n) (m j : ℕ → ℕ)
    (hmk : ∀ᶠ n : ℕ in Filter.atTop, m n * 2 ^ j n < n ∧ j n + 1 < m n)
    (C : List Bool → List Bool → List Bool)
    (hC : EvaluableInSpace C (fun n => m n - j n - 1) (fun n => m n * 2 ^ j n) S)
    (hAv : ¬ ∃ (M : Machine 2) (a : ℕ), IsPolyNTime M a ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x : List Bool, x.length = n →
        SolvesAvoidNDB M C (fun n => m n - j n - 1) (fun n => m n * 2 ^ j n)
          (fun n => a * (n ^ a + 1)) x) :
    ¬ ∃ (H : Machine 2) (a : ℕ), IsSearchNPGen H a (fun n => 2 ^ j n) m ∧
      ∀ (D : Machine 3) (K : ℕ), OneWayTape D 2 →
        (∀ x r w : List Bool, r.length = m x.length →
          HaltsWithin D ![x, r, w] ⌈(2 : ℝ) ^ (K * (S x.length + 1))⌉₊ ∧
          (workSpace D ![x, r, w] : ℝ) ≤ K * (S x.length + (m x.length - j x.length - 1 : ℕ) + 1)) →
        HitsTargeted H a (fun n => 2 ^ j n) m
          (fun x r => coNDAccepts D ⌈(2 : ℝ) ^ (K * (S x.length + 1))⌉₊ x r) (1 / 2) := by sorry

end AvoidPlast.Supplement
