-- Prove2me | Theorems.Thm_BookProof_MassGap_shiftedSpectrum_vacuum
-- name    : BookProof.MassGap.shiftedSpectrum_vacuum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:37:45.747836+00:00
-- url     : https://prove2.me/theorems/a146408e-b19e-4dae-9ac3-7a2f62b4c6cd
-- title:
--   Vacuum energy is unchanged by the number-operator shift
-- statement:
--   Vacuum energy is unchanged by the number-operator shift.
--
--   Let $E$ be an energy assignment on the $(n+2)$-level spectrum and $\lambda$ the shift amount. The shifted spectrum is $E_i + \lambda \cdot n_i$, where $n_i$ is the eigenvalue of the number operator at level $i$. At the vacuum level $i = 0$ the number-operator eigenvalue is $0$, so
--   $$
--   \text{shiftedSpectrum}(E,\lambda,0)=E_0.
--   $$
--
--   This is the 'no observable consequence' half of the mass-gap argument: adding the number operator to the Hamiltonian leaves the vacuum energy untouched.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MassGap.shiftedSpectrum_vacuum` (module `BookProof.MassGap`), line-linked source: `ChapterMassGap.lean` lines 127–129.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMassGap.lean#L127-L129

-- Generated from ChapterMassGap.lean — theorem BookProof.MassGap.shiftedSpectrum_vacuum
import Mathlib
import Definitions.Def_ChapterMassGap
open BookProof.MassGap

















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]




variable {n : ℕ}

theorem BookProof.MassGap.shiftedSpectrum_vacuum (E : Fin (n + 2) → ℝ) (lam : ℝ) :
    shiftedSpectrum E lam 0 = E 0 := by sorry
