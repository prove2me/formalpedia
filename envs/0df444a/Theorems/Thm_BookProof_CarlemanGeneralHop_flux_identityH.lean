-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_flux_identityH
-- name    : BookProof.CarlemanGeneralHop.flux_identityH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-11T06:51:31.610517+00:00
-- url     : https://prove2.me/theorems/ebba37c6-57d4-46df-b620-14730c8d29ba
-- title:
--   `BookProof.CarlemanGeneralHop.flux_identityH` (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) → c' h (hshift (p h) (m h) b) = c h b) (hvanL : ∀ (h : ι) (a : Fin d...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.flux_identityH` (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) → c' h (hshift (p h) (m h) b) = c h b) (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0) (hrec : LadderRecH u lam p m c c' w z) (N : ℕ) : z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) = ∑ h : ι, ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h), rtG u (w h) (c h) (p h) (m h) a).im - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N, rtG u (w h) (c h) (p h) (m h) b).im)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.flux_identityH`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.flux_identityH
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
open BookProof.HermiteCarleman
open BookProof.CarlemanGeneralHop



open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {ι : Type*} [Fintype ι] {lam : (Fin d →₀ ℕ) → ℝ} {p m : ι → (Fin d →₀ ℕ)}
variable {c c' : ι → (Fin d →₀ ℕ) → ℝ} {w : ι → ℂ} {z : ℂ}

theorem BookProof.CarlemanGeneralHop.flux_identityH
    (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) →
      c' h (hshift (p h) (m h) b) = c h b)
    (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0)
    (hrec : LadderRecH u lam p m c c' w z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = ∑ h : ι, ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
            rtG u (w h) (c h) (p h) (m h) a).im
          - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
            rtG u (w h) (c h) (p h) (m h) b).im) := by sorry
