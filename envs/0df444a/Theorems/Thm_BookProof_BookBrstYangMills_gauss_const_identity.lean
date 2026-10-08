-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gauss_const_identity
-- name    : BookProof.BookBrstYangMills.gauss_const_identity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:10:35.045269+00:00
-- url     : https://prove2.me/theorems/af05f1b3-b322-4789-a6c8-32351015d62a
-- title:
--   `BookProof.BookBrstYangMills.gauss_const_identity` (μ : Fin 4) (a c e : Fin N) : (∑ b, G.f a b e * (-(G.D μ c b))) - (∑ b, G.f a b c * (-(G.D μ e b))) = ∑ h, G.f c e h * (-(G.D μ h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gauss_const_identity` (μ : Fin 4) (a c e : Fin N) : (∑ b, G.f a b e * (-(G.D μ c b))) - (∑ b, G.f a b c * (-(G.D μ e b))) = ∑ h, G.f c e h * (-(G.D μ h a))
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gauss_const_identity`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gauss_const_identity
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gauss_const_identity (μ : Fin 4) (a c e : Fin N) :
    (∑ b, G.f a b e * (-(G.D μ c b))) - (∑ b, G.f a b c * (-(G.D μ e b)))
      = ∑ h, G.f c e h * (-(G.D μ h a)) := by sorry
