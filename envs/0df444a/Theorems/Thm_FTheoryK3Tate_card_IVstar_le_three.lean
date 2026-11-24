-- Prove2me | Theorems.Thm_FTheoryK3Tate_card_IVstar_le_three
-- name    : FTheoryK3Tate.card_IVstar_le_three
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:56:21.735403+00:00
-- url     : https://prove2.me/theorems/ccc6602b-b273-485a-90d0-ed27756d4b3a
-- title:
--   card_IVstar_le_three
-- statement:
--   On a characteristic-zero K3-degree model, the set of type $\mathrm{IV}^*$ ($E_6$) points is finite and has at most three elements: each contributes $8$ to the discriminant budget and $4 \times 8 = 32 > 24$.
-- source:
--   Kodaira/Tate classification of singular fibres: J. Tate (LNM 476, 1975); M. Schuett, T. Shioda, Elliptic Surfaces, arXiv:0907.0298; F-theory dictionary: T. Weigand, TASI Lectures on F-theory, arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Corollary (`E6` cap). On a Calabi–Yau/K3 model the set of type IV\* (`E6`) points is finite
    and has at most three elements — each contributes `8` to the discriminant budget and
    `4 × 8 = 32 > 24`. -/
theorem card_IVstar_le_three (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar}.Finite ∧
    Nat.card {t₀ : k | HasKodaira f g t₀ Kodaira.IVstar} ≤ 3 := by
  sorry
end FTheoryK3Tate
