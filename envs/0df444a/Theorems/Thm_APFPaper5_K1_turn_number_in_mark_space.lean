-- Prove2me | Theorems.Thm_APFPaper5_K1_turn_number_in_mark_space
-- name    : APFPaper5.K1.turn_number_in_mark_space
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:02:02.555586+00:00
-- url     : https://prove2.me/theorems/46eccff0-7a36-4e2c-a369-ab9115b44613
-- title:
--   A score-preserving map fixing a total has constrained turn coordinates
-- statement:
--   Let B be real-bilinear. Supply e,z,w with self-scores two and all six ordered cross scores zero. Assume T is additive and real-homogeneous, preserves every B-score, fixes e, and satisfies Tz=αe+xz+yw. Then α=0 and x²+y²=1. With p=(e+z)/2 and p′=(e−z)/2, the theorem also gives B(p,Tp)=(1+x)/2 and B(p′,Tp)=(1−x)/2. The directions and linear action are supplied; this computes their constrained coordinates without constructing a physical third direction or proving a global rotation representation.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_rank_three.lean:62; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;3038-3041; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_three_yeses_2026-11-12.md, 1 and standing

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem APFPaper5.K1.turn_number_in_mark_space (B : V → V → ℝ) (hB : IsBilinear B) (e z w : V) (T : V → V)
    (alpha x y : ℝ)
    (hee : B e e = 2) (hzz : B z z = 2) (hww : B w w = 2)
    (hez : B e z = 0) (hze : B z e = 0) (hew : B e w = 0) (hwe : B w e = 0)
    (hzw : B z w = 0) (hwz : B w z = 0)
    (hTadd : ∀ a b : V, T (a + b) = T a + T b)
    (hTsmul : ∀ (r : ℝ) (a : V), T (r • a) = r • T a)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b) (hTe : T e = e)
    (hTz : T z = alpha • e + x • z + y • w) :
    alpha = 0 ∧ x * x + y * y = 1 ∧
      B ((1 / 2 : ℝ) • (e + z)) (T ((1 / 2 : ℝ) • (e + z))) = (1 + x) / 2 ∧
      B ((1 / 2 : ℝ) • (e + (-1 : ℝ) • z)) (T ((1 / 2 : ℝ) • (e + z))) = (1 - x) / 2 := by sorry
