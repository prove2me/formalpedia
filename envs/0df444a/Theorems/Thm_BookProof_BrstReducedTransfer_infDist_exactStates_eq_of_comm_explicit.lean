-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_infDist_exactStates_eq_of_comm_explicit
-- name    : BookProof.BrstReducedTransfer.infDist_exactStates_eq_of_comm_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:46.385723+00:00
-- url     : https://prove2.me/theorems/643c6427-7bc4-4cd8-94ff-fa4ab5277561
-- title:
--   A commuting flow preserves the distance to the exact states
-- statement:
--   Let $U$ be a one-parameter unitary flow on $H$ (with $U(0) = 1$, the group law and isometry properties) that commutes with the gauge projection $\mathrm{Om}$.  Then for every $t$ and $x$,
--   $$\mathrm{infDist}\big(U_t x, \mathrm{exactStates}\big) = \mathrm{infDist}\big(x, \mathrm{exactStates}\big).$$
--
--   Because $U_t$ is a bijection of $H$ preserving the gauge-invariant subspace, it maps the set of exact (pure-gauge) states onto itself, so the infimum distance is transported rather than merely bounded.  This is what makes the BRST distance-to-exact-states a conserved quantity of the flow.
--
--   Corrected statement of the retired node `BookProof.BrstReducedTransfer.infDist_exactStates_eq`: the commutation hypothesis `hcomm` was a section variable not occurring in the type, so the published target quantified over flows that do not commute with $\mathrm{Om}$; it is an explicit binder here.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterBrstReducedTransfer.lean

-- Corrected statement of BookProof.BrstReducedTransfer.infDist_exactStates_eq.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterBrstReducedTransfer.lean (Lean 4.28) and timepiece331/BookProof/ChapterBrstReducedTransfer.lean (Lean 4.33.1).
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))

theorem BookProof.BrstReducedTransfer.infDist_exactStates_eq_of_comm_explicit (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y)) (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) : Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by sorry
