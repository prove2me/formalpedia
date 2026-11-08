-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_ltG_eq_conj_rtG
-- name    : BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:41:54.520472+00:00
-- url     : https://prove2.me/theorems/7eb1f8b2-f467-4ac8-8e87-72871179dbb9
-- title:
--   `BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG` {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m a : Fin d →₀ ℕ} (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG` {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m a : Fin d →₀ ℕ} (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m b) = c b) (ha : ∀ k, p k ≤ a k) : ltG u w c' p m a = (starRingEnd ℂ) (rtG u w c p m (hshift m p a))
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
open BookProof.CarlemanGeneralHop



open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}

theorem BookProof.CarlemanGeneralHop.ltG_eq_conj_rtG {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m a : Fin d →₀ ℕ}
    (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m b) = c b)
    (ha : ∀ k, p k ≤ a k) :
    ltG u w c' p m a = (starRingEnd ℂ) (rtG u w c p m (hshift m p a)) := by sorry
