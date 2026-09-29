-- Prove2me | Theorems.Thm_BookProof_MassGap_shiftedSpectrum_excited
-- name    : BookProof.MassGap.shiftedSpectrum_excited
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:37:00.944094+00:00
-- url     : https://prove2.me/theorems/339bbd16-f76c-4c0f-b800-c8612d7bff4c
-- title:
--   Every excited energy is shifted by exactly $\lambda$
-- statement:
--   Every excited energy is shifted by exactly $\lambda$.
--
--   For a non-vacuum level $i \neq 0$ the number operator has eigenvalue $1$, so the shifted spectrum is
--   $$
--   \text{shiftedSpectrum}(E,\lambda,i)=E_i+\lambda.
--   $$
--
--   Together with `shiftedSpectrum_vacuum` this gives the complete spectrum of the number-operator-shifted Hamiltonian: a rigid shift of the excited states by $\lambda$.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MassGap.shiftedSpectrum_excited` (module `BookProof.MassGap`), line-linked source: `ChapterMassGap.lean` lines 134–137.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMassGap.lean#L134-L137

-- Generated from ChapterMassGap.lean — theorem BookProof.MassGap.shiftedSpectrum_excited
import Mathlib
import Definitions.Def_ChapterMassGap
open BookProof.MassGap

















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]




variable {n : ℕ}

theorem BookProof.MassGap.shiftedSpectrum_excited (E : Fin (n + 2) → ℝ) (lam : ℝ)
    {i : Fin (n + 2)} (hi : i ≠ 0) :
    shiftedSpectrum E lam i = E i + lam := by sorry
