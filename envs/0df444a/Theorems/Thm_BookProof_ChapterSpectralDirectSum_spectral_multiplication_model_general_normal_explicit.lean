-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_spectral_multiplication_model_general_normal_explicit
-- name    : BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_normal_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:50.976478+00:00
-- url     : https://prove2.me/theorems/8f775b38-363a-4b9e-a8fa-1ac14c7632b4
-- title:
--   Spectral theorem, multiplication-model form, for normal operators
-- statement:
--   Let $T$ be a bounded normal operator on a complex Hilbert space $H$.  Then $H$ splits as a direct integral of $L^2$ spaces over the spectrum,
--   $$H \cong \int^{\oplus}_{S} L^{2}\big(\sigma(T), \mu_{x}\big)\,d\nu(x),$$
--   in such a way that under the isometry $V$ the operator $T$ becomes multiplication by the coordinate function: $V_x(\mathrm{mulRep}(\mu_x, \mathrm{coordFn}\,T)\,u) = T(V_x u)$ for every $x$ and every $u$.  Each $\mu_x$ is a probability measure on the spectrum, and the family is realised as a Hilbert sum.
--
--   Normality — not self-adjointness — is what the proof needs: it guarantees that the multiplication representation is isometric on $L^2$ of the spectral measure.
--
--   Corrected statement of the retired node `BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general`: the hypothesis `hT : IsStarNormal T` did not occur in the type, so the published target quantified over *arbitrary* bounded operators, which is false; it is an explicit binder here.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSpectralDirectSum.lean

-- Corrected statement of BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterSpectralDirectSum.lean (Lean 4.28) and timepiece331/BookProof/ChapterSpectralDirectSum.lean (Lean 4.33.1).
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
open BookProof.ChapterSpectralDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

theorem BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general_normal_explicit (hT : IsStarNormal T) : ∃ (S : Set H) (mu : S → Measure (spectrum ℂ T)) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H), (∀ x : S, IsProbabilityMeasure (mu x)) ∧ IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧ (∀ (x : S) (u : Lp ℂ 2 (mu x)), V x (mulRep (mu x) (coordFn T) u) = T (V x u)) := by sorry
