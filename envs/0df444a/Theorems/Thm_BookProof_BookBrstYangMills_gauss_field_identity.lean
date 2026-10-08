-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gauss_field_identity
-- name    : BookProof.BookBrstYangMills.gauss_field_identity
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:10:48.890978+00:00
-- url     : https://prove2.me/theorems/73c4ac20-cb4b-47eb-8a30-a73bd5b5c775
-- title:
--   `BookProof.BookBrstYangMills.gauss_field_identity` (a c e g : Fin N) : (∑ b, G.f a b e * G.f b g c) - (∑ b, G.f a b c * G.f b g e) = ∑ h, G.f c e h * G.f a g h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gauss_field_identity` (a c e g : Fin N) : (∑ b, G.f a b e * G.f b g c) - (∑ b, G.f a b c * G.f b g e) = ∑ h, G.f c e h * G.f a g h
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gauss_field_identity`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gauss_field_identity
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gauss_field_identity (a c e g : Fin N) :
    (∑ b, G.f a b e * G.f b g c) - (∑ b, G.f a b c * G.f b g e)
      = ∑ h, G.f c e h * G.f a g h := by sorry
