-- Prove2me | Theorems.Thm_CannonFloydParry_exists_standardDyadicPartitions_of_mem_V
-- name    : CannonFloydParry.exists_standardDyadicPartitions_of_mem_V
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:21:59.055098+00:00
-- url     : https://prove2.me/theorems/1a510a12-3e26-4970-b156-ab2c4d7f781f
-- title:
--   p. 240 — every element of $V$ is given by a labelled tree pair
-- statement:
--   For every $f \in V$ there are standard dyadic partitions $0 = x_0 < \dots < x_n = 1$ and $0 = y_0 < \dots < y_n = 1$ with the same number of intervals, and a permutation $\sigma$ of $\{0, \dots, n-1\}$, such that $f$ maps each $[x_i, x_{i+1})$ onto $[y_{\sigma(i)}, y_{\sigma(i)+1})$ by $[z] \mapsto [y_{\sigma(i)} + 2^k(z - x_i)]$, where $2^k$ is the ratio of the two lengths.
--
--   **Formalization Note.** A standard dyadic partition is the §2 bundle's `IsStandardDyadicPartition`, the partition cut out by the leaves of a tree; the pair of partitions with $\sigma$ is the source's tree diagram "with labelled leaves".
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 240, tree diagrams for V

import Mathlib
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_standardDyadicPartitions_of_mem_V {f : Equiv.Perm UnitAddCircle} (hf : f ∈ V) :
    ∃ (n : ℕ) (x y : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)),
      IsStandardDyadicPartition (List.ofFn x) ∧ IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ i : Fin n, ∃ k : ℤ, y (σ i).succ - y (σ i).castSucc = 2 ^ k * (x i.succ - x i.castSucc) ∧
        ∀ z ∈ Set.Ico (x i.castSucc) (x i.succ),
          f (z : UnitAddCircle) = ((y (σ i).castSucc + 2 ^ k * (z - x i.castSucc) : ℝ) : UnitAddCircle) := by
  sorry

end CannonFloydParry
