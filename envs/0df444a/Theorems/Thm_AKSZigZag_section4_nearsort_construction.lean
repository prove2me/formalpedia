-- Prove2me | Theorems.Thm_AKSZigZag_section4_nearsort_construction
-- name    : AKSZigZag.section4_nearsort_construction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:23.682846+00:00
-- url     : https://prove2.me/theorems/157a33ce-1586-4bc3-976b-91b5fce0b71e
-- title:
--   §4, p.5 — recursive $\varepsilon_1$-halving is an $\varepsilon$-nearsort of bounded depth
-- statement:
--   There is $\varepsilon_0>0$ with the following property. Let $0<\varepsilon<\varepsilon_0$ and $\varepsilon_1<\varepsilon/\log_2(1/\varepsilon)$. Let $h_k$ be, for every $k$, a standard $\varepsilon_1$-halver on $k$ registers of depth at most $d$.
--
--   Build the network that applies $h$ to all $m$ registers, then to both halves, then to the quarters, eighths, …, until the pieces have size $w<\varepsilon m$. This network is a standard $\varepsilon$-nearsort on $m$ registers, and its depth is at most a bound $D$ that does not depend on $m$.
--
--   With the halvers of §3, this provides the bounded-depth $\varepsilon$-nearsorts that the zig-zag algorithm applies in every step.
--
--   Differences from the source:
--   - reading: ε fixed (small), ε₁ < ε/log(1/ε) → ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), ε₁ < ε / log₂(1/ε); reason: the paper takes ε small throughout (§1, p.2; §8, p.7) and all logarithms base 2 (§5); for large ε the claim fails (ε = 0.9: ε₁ = 5 admits the identity network as halver, and the reversed permutation of 100 elements is not 0.9-nearsorted)
--   - reading: until the pieces have size w < εm → a piece is halved iff it has ≥ 2 registers and size ≥ εm; its lower half has ⌊size/2⌋ registers; reason: a single register cannot be halved; ⌊·/2⌋ is §3's split A = (1,...,⌊m/2⌋)
--   - encoding: the obtained network of bounded depth → given halvers of depth ≤ d, ∃ D, ∀ m, depth ≤ D; reason: bounded independently of m
--   - generalization: an ε₁-halver with ε₁ < ε/log(1/ε) → any ε₁ below ε/log₂(1/ε), any family of standard ε₁-halvers; reason: the paper's choice is one such family
-- source:
--   Ajtai, Komlós, Szemerédi, An O(n log n) Sorting Network, STOC 1983, doi:10.1145/800061.808726, §4, p.5 ("To construct an ε-nearsort network …")

import Mathlib
import Definitions.Def_AKSSorting_Core_ComparatorNetwork
import Definitions.Def_AKSZigZag_IsStandard
import Definitions.Def_AKSZigZag_IsHalver
import Definitions.Def_AKSZigZag_IsNearsort
import Definitions.Def_AKSZigZag_halvingNearsort

namespace AKSZigZag

open AKSSorting.Core

/-- **Recursive halving is a bounded-depth ε-nearsort** (AKS, STOC 1983,
doi:10.1145/800061.808726, §4, p.5): "To construct an ε-nearsort network, apply an ε1-halver
(network), with ε1 < ε/log(1/ε), to the whole set of registers, then apply ε1-halvers to the top
and bottom half of registers, then to each quarter, eighth, sixteenth, until the pieces have size
w < εm. It is easy to see that the obtained network of bounded depth is an ε-nearsort."

There is `ε₀ > 0` such that for every `ε ∈ (0, ε₀)` and every `ε₁ < ε / log₂(1/ε)`: if `h k` is a
standard ε₁-halver on `k` registers for every `k`, of depth at most `d`, then the recursive
halving network `halvingNearsort h ε m` is, for every `m`, a standard ε-nearsort of depth at most
some `D` that does not depend on `m`.

**Formalization Note.** `log` is `log₂` (§5: "All logarithms are to the base 2"). `ε₀` is the
paper's standing "ε small": the claim fails for large `ε` (at `ε = 0.9`, `ε₁ = 5` allows the
identity network as halver, and the reversed permutation of 100 elements is not
0.9-nearsorted). -/
theorem section4_nearsort_construction :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ ε₁ : ℝ, ε₁ < ε / Real.logb 2 (1 / ε) →
      ∀ h : (k : ℕ) → ComparatorNetwork k, (∀ k, IsStandard (h k) ∧ IsHalver ε₁ (h k)) →
      ∀ d : ℕ, (∀ k, (h k).depth ≤ d) →
      ∃ D : ℕ, ∀ m : ℕ,
        IsStandard (halvingNearsort h ε m) ∧ (halvingNearsort h ε m).depth ≤ D ∧
          IsNearsort ε (halvingNearsort h ε m) := by sorry

end AKSZigZag
