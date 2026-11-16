-- Prove2me | Theorems.Thm_CatalyticSorting494_Sorting_Supplement_theorem_1_4
-- name    : CatalyticSorting494.Sorting.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:19:58.682325+00:00
-- url     : https://prove2.me/theorems/b94c2abc-3f9f-4288-8d1f-ad10bb65ffeb
-- title:
--   Theorem 1.4 — catalytic integer matrix multiplication in $n^{\omega+o(1)}$ time and $O(\log n)$ clean space
-- statement:
--   Fix $p\in\mathbb N$. There is a single catalytic algorithm in the dirty-XOR-output model which takes two $n\times n$ matrices $X,Y$ with integer entries in $\{0,\dots,(n+1)^p\}$ and computes their integer product $XY$, using
--
--   $$\text{time } n^{\omega+o(1)},\qquad \text{clean space } O(\log n),\qquad \text{catalytic space } n^{\omega+o(1)},$$
--
--   where $\omega$ is the matrix multiplication exponent of Definition 4.10.
--
--   Precisely: there are one machine $M$, one capacity function $c$, one constant $A$ and one function $\varepsilon:\mathbb N\to\mathbb R$ with $\varepsilon(n)\to0$, such that for all $n\ge1$, $c(n)\le A\,n^{\omega+\varepsilon(n)}$, and for all such $X,Y$ and every initial catalytic content $z$ of length $c(n)$, $M$ halts within $A\,n^{\omega+\varepsilon(n)}$ steps with at most $A(\log_2 n+1)$ charged clean bits, having XORed the entries of $XY$ (fixed-width binary fields) into the beginning of the catalytic tape and restored all other catalytic bits.
--
--   This is a companion theorem of the mission, not used in the proof of the sorting corollary; the paper derives it from Corollary 4.11 (printed p.18), which multiplies matrices over $\mathbb Z/m\mathbb Z$, by taking $m$ larger than every entry of $XY$.
--
--   Differences from the source:
--   - generalization: A, B ∈ [poly(n)]^{n×n}, [N] = {1,…,N} → for every p : ℕ, entries in {0,…,(n+1)^p}; reason: every polynomial bound q(n) is at most (n+1)^p for all n ≥ 1 for some p, and entry 0 adds inputs; one algorithm per p, as one per polynomial in the source
--   - generalization: no catalytic space bound stated in Theorem 1.4 → catalytic capacity c(n) ≤ A·n^{ω+ε(n)}; reason: the bound proved in Corollary 4.11 (dirty space n^{ω+o(1)} polylog m), stated under the paper's §2 convention of giving catalytic space explicitly; dropping the conjunct gives the source's statement
--   - encoding: n^{ω+o(1)} time, O(log n) clean space → one function ε : ℕ → ℝ with ε → 0 fixed before the instance, time A·n^{ω+ε(n)}, clean space A·(⌊log₂ n⌋+1); reason: the standard meaning of o(1) for one algorithm; the +1 covers n = 1
--   - encoding: integer matrices and their product AB → natural-number matrices written as fixed-width binary fields; output the exact product, each entry in ⌊log₂(n(n+1)^{2p})⌋+1 bits, in the dirty-XOR-output model; reason: entries are nonnegative; the width holds every entry of AB
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Theorem 1.4, printed p.3 (PDF p.4); proved via Corollary 4.11, printed p.18 (PDF p.19); ω is Definition 4.10, printed p.18 (PDF p.19)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine
import Definitions.Def_CatalyticSorting494_Sorting_Supplement_MatrixMultiplication

open CatalyticSorting494.Sorting
open Filter Topology

namespace CatalyticSorting494.Sorting.Supplement

/-- Theorem 1.4. For every polynomial entry bound `(n + 1)^p`, one machine `M`, one capacity function
`c`, one constant `A` and one exponent function `ε → 0` work for all `n ≥ 1`, all pairs of `n × n`
matrices with entries in `{0, …, (n + 1)^p}` and all initial catalytic contents. `ω` is
Definition 4.10. -/
theorem theorem_1_4 (p : ℕ) :
    ∃ (M : Machine) (c : ℕ → ℕ) (A : ℕ) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n →
        ((c n : ℝ) ≤ A * (n : ℝ) ^ (omega + ε n)) ∧
        ∀ X Y : Matrix (Fin n) (Fin n) ℕ,
          (∀ i j, X i j ≤ (n + 1) ^ p) → (∀ i j, Y i j ≤ (n + 1) ^ p) →
          ∀ z : List Bool, z.length = c n →
            ComputesWithin M (encodeMatrices n p X Y) z (productOutput n p X Y)
              (A * (n : ℝ) ^ (omega + ε n))
              (A * (Nat.log 2 n + 1)) := by sorry

end CatalyticSorting494.Sorting.Supplement
