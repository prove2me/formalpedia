-- Prove2me | Theorems.Thm_BookProof_MassGap_heisenberg_number_shift_invariant
-- name    : BookProof.MassGap.heisenberg_number_shift_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:58:46.306723+00:00
-- url     : https://prove2.me/theorems/6d96b6bf-e808-4a8f-88d5-5b7a2f3f20f3
-- title:
--   Headline (observable invariance).** If the Hamiltonian `H` and every observable `Obs` commute with the number operator `N`, then the Heisenberg evolution of `Obs` under the number-shifted
-- statement:
--   **Headline (observable invariance).** If the Hamiltonian `H` and every
--   observable `Obs` commute with the number operator `N`, then the Heisenberg
--   evolution of `Obs` under the number-shifted Hamiltonian `H + λ N` coincides with
--   its evolution under `H` for every scalar `t` and shift `λ`. The mass-gap shift by
--   `λ N` has *no observable consequence*.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MassGap.heisenberg_number_shift_invariant` (module `BookProof.MassGap`), line-linked source: `ChapterMassGap.lean` lines 74–96.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMassGap.lean#L74-L96

-- Generated from ChapterMassGap.lean — theorem BookProof.MassGap.heisenberg_number_shift_invariant
import Mathlib
import Definitions.Def_ChapterMassGap
open BookProof.MassGap

















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem BookProof.MassGap.heisenberg_number_shift_invariant (H N Obs : 𝔸) (t lam : ℂ)
    (hHN : Commute H N) (hON : Commute Obs N) :
    NormedSpace.exp (t • (H + lam • N)) * Obs * NormedSpace.exp (-(t • (H + lam • N)))
      = NormedSpace.exp (t • H) * Obs * NormedSpace.exp (-(t • H)) := by sorry
