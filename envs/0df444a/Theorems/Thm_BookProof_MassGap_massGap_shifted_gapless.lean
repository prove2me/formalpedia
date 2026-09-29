-- Prove2me | Theorems.Thm_BookProof_MassGap_massGap_shifted_gapless
-- name    : BookProof.MassGap.massGap_shifted_gapless
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:36:23.488572+00:00
-- url     : https://prove2.me/theorems/6c745035-7707-4db6-b14f-82813c912836
-- title:
--   Headline (arbitrary mass gap): for the gapless free field the number-operator shift produces a mass gap equal to $\lambda$
-- statement:
--   Headline (arbitrary mass gap): for the gapless free field the number-operator shift produces a mass gap equal to $\lambda$.
--
--   Take the free (gapless) field $E \equiv 0$ on the $(n+2)$-level spectrum and shift by the number operator scaled by $\lambda$. The mass gap — the least excited-state energy — becomes exactly
--   $$
--   \text{massGap}(\text{shiftedSpectrum}(0,\lambda))=\lambda.
--   $$
--
--   Since $\lambda$ is arbitrary, the mass gap can be set to any prescribed value without changing the observables (the vacuum is untouched), which is the formal core of the mass-gap argument in the book.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MassGap.massGap_shifted_gapless` (module `BookProof.MassGap`), line-linked source: `ChapterMassGap.lean` lines 144–153.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMassGap.lean#L144-L153

-- Generated from ChapterMassGap.lean — theorem BookProof.MassGap.massGap_shifted_gapless
import Mathlib
import Definitions.Def_ChapterMassGap
open BookProof.MassGap

















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]




variable {n : ℕ}

theorem BookProof.MassGap.massGap_shifted_gapless (lam : ℝ) :
    massGap (shiftedSpectrum (fun _ : Fin (n + 2) => (0 : ℝ)) lam) = lam := by sorry
