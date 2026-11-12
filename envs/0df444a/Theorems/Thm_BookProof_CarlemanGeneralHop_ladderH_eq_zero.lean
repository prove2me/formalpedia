-- Prove2me | Theorems.Thm_BookProof_CarlemanGeneralHop_ladderH_eq_zero
-- name    : BookProof.CarlemanGeneralHop.ladderH_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T19:36:48.433235+00:00
-- url     : https://prove2.me/theorems/53599c7e-9420-452d-bf06-e74cb82c46fc
-- title:
--   `BookProof.CarlemanGeneralHop.ladderH_eq_zero` {B Camp : ℝ} (hz : z.im ≠ 0) (hCamp : 0 ≤ Camp) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (hp : ∀ (h :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanGeneralHop`.
--
--   `BookProof.CarlemanGeneralHop.ladderH_eq_zero` {B Camp : ℝ} (hz : z.im ≠ 0) (hCamp : 0 ≤ Camp) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (hp : ∀ (h : ι) (k : Fin d), p h k ≤ 2) (hm1 : ∀ (h : ι) (k : Fin d), m h k ≤ 1) (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) → c' h (hshift (p h) (m h) b) = c h b) (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0) (hvanR : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, m h k ≤ a k) → c h a = 0) (hbnd : ∀ (h : ι) (a : Fin d →₀ ℕ) (N : ℕ), (∀ k, a k ≤ N) → |c h a| ≤ Camp * ((N : ℝ) + 1)) (hrec : LadderRecH u lam p m c c' w z) : ∀ a, u a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanGeneralHop.ladderH_eq_zero`.

-- Generated from ChapterCarlemanGeneralHop.lean — theorem BookProof.CarlemanGeneralHop.ladderH_eq_zero
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

theorem BookProof.CarlemanGeneralHop.ladderH_eq_zero {B Camp : ℝ} (hz : z.im ≠ 0) (hCamp : 0 ≤ Camp)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hp : ∀ (h : ι) (k : Fin d), p h k ≤ 2) (hm1 : ∀ (h : ι) (k : Fin d), m h k ≤ 1)
    (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) →
      c' h (hshift (p h) (m h) b) = c h b)
    (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0)
    (hvanR : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, m h k ≤ a k) → c h a = 0)
    (hbnd : ∀ (h : ι) (a : Fin d →₀ ℕ) (N : ℕ), (∀ k, a k ≤ N) →
      |c h a| ≤ Camp * ((N : ℝ) + 1))
    (hrec : LadderRecH u lam p m c c' w z) : ∀ a, u a = 0 := by sorry
