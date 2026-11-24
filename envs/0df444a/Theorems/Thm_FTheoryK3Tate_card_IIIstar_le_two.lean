-- Prove2me | Theorems.Thm_FTheoryK3Tate_card_IIIstar_le_two
-- name    : FTheoryK3Tate.card_IIIstar_le_two
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:56:10.993812+00:00
-- url     : https://prove2.me/theorems/2b0a84e4-9038-49a0-b6d6-cd895b5fb00e
-- title:
--   card_IIIstar_le_two
-- statement:
--   On a characteristic-zero K3-degree model, the set of type $\mathrm{III}^*$ ($E_7$) points is finite and has at most two elements: each contributes $9$ and $3 \times 9 = 27 > 24$.
-- source:
--   Kodaira/Tate classification of singular fibres: J. Tate (LNM 476, 1975); M. Schuett, T. Shioda, Elliptic Surfaces, arXiv:0907.0298; F-theory dictionary: T. Weigand, TASI Lectures on F-theory, arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Corollary (`E7` cap). On a Calabi–Yau/K3 model the set of type III\* (`E7`) points is finite
    and has at most two elements — each contributes `9` to the discriminant budget and
    `3 × 9 = 27 > 24`. -/
theorem card_IIIstar_le_two (f g : k[X]) (h : IsK3Data f g) :
    {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar}.Finite ∧
    Nat.card {t₀ : k | HasKodaira f g t₀ Kodaira.IIIstar} ≤ 2 := by
  sorry
end FTheoryK3Tate
