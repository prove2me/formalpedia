-- Prove2me | Theorems.Thm_BookProof_ChapterElectroweakFieldStrength_electroweak_fieldStrength
-- name    : BookProof.ChapterElectroweakFieldStrength.electroweak_fieldStrength
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:43:10.508804+00:00
-- url     : https://prove2.me/theorems/5e1b12f8-62ad-4343-af68-e3b1d009ed4d
-- title:
--   `BookProof.ChapterElectroweakFieldStrength.electroweak_fieldStrength` (g : ℂ) (hg : g ≠ 0) (G Wμ Wν : Fin 3 → ℂ) (j : Fin 3) : proj g (Fmat g G Wμ Wν) j = G j - g * ∑ k, ∑ l, eps j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterElectroweakFieldStrength`.
--
--   `BookProof.ChapterElectroweakFieldStrength.electroweak_fieldStrength` (g : ℂ) (hg : g ≠ 0) (G Wμ Wν : Fin 3 → ℂ) (j : Fin 3) : proj g (Fmat g G Wμ Wν) j = G j - g * ∑ k, ∑ l, eps j k l * Wμ k * Wν l
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterElectroweakFieldStrength.electroweak_fieldStrength`.

-- Generated from ChapterElectroweakFieldStrength.lean — theorem BookProof.ChapterElectroweakFieldStrength.electroweak_fieldStrength
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParitySU2
open BookProof.ChapterElectroweakFieldStrength


open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

theorem BookProof.ChapterElectroweakFieldStrength.electroweak_fieldStrength (g : ℂ) (hg : g ≠ 0) (G Wμ Wν : Fin 3 → ℂ) (j : Fin 3) :
    proj g (Fmat g G Wμ Wν) j = G j - g * ∑ k, ∑ l, eps j k l * Wμ k * Wν l := by sorry
