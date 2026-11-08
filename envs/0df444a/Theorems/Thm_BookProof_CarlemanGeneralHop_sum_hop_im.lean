-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_sum_hop_im
-- name    : BookProof.CarlemanGeneralHop.sum_hop_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:41:47.568693+00:00
-- url     : https://prove2.me/theorems/8bf45bd3-4829-4f04-8281-ff6c9a2a87aa
-- title:
--   `BookProof.CarlemanGeneralHop.sum_hop_im` {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ} (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m b) = c...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.sum_hop_im` {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ} (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m b) = c b) (hvanL : ∀ a : Fin d →₀ ℕ, ¬ (∀ k, p k ≤ a k) → c' a = 0) (A : Finset (Fin d →₀ ℕ)) : (∑ a ∈ A, (rtG u w c p m a + ltG u w c' p m a)).im = (∑ a ∈ A \ hopB A p m, rtG u w c p m a).im - (∑ b ∈ hopB A p m \ A, rtG u w c p m b).im
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.sum_hop_im`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.sum_hop_im
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

theorem BookProof.CarlemanGeneralHop.sum_hop_im {w : ℂ} {c c' : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ}
    (hcomp : ∀ b : Fin d →₀ ℕ, (∀ k, m k ≤ b k) → c' (hshift p m b) = c b)
    (hvanL : ∀ a : Fin d →₀ ℕ, ¬ (∀ k, p k ≤ a k) → c' a = 0) (A : Finset (Fin d →₀ ℕ)) :
    (∑ a ∈ A, (rtG u w c p m a + ltG u w c' p m a)).im
      = (∑ a ∈ A \ hopB A p m, rtG u w c p m a).im
        - (∑ b ∈ hopB A p m \ A, rtG u w c p m b).im := by sorry
