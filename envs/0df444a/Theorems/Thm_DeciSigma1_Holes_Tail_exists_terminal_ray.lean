-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_terminal_ray
-- name    : DeciSigma1.Holes.Tail.exists_terminal_ray
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:11.424228+00:00
-- url     : https://prove2.me/theorems/723d0d56-8834-4892-928a-04dba22e2e60
-- title:
--   Tail: exists terminal ray
-- statement:
--   If the longest suffix of `w` with period at most `periodBound m` has at least
--   `terminalLengthBound m` letters, the last `h = p · N!` letters of `w`, for the period `p` of that
--   suffix, form a factor closed at a window `B'` after the first rejected cut; the interval
--   `[c - B', |w|)` has period `p`, and no occurrence of the suffix of length `B'` of a target with
--   chain budget `fixedChainBudget (m + 1)` ends inside the factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L134-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/TerminalRays.lean#L134-L189

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {σ : ℕ} [DecidableEq α] [Fintype S]

theorem DeciSigma1.Holes.Tail.exists_terminal_ray (C : LevelBounds σ k (Fintype.card S)) {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) {m : ℕ}
    (hT : C.terminalLengthBound m ≤ longestPeriodicSuffixLength (C.periodBound m) (W i)) :
    ∃ B c p, ClosedAt M.toTable (M.start i) (W i) B c (W i).length ∧ M.firstRejection W i ≤ c ∧
      0 < p ∧ p ≤ C.periodBound m ∧ (W i).length - c = p * (Fintype.card S).factorial ∧
      PeriodicOn (W i) p (c - B) (W i).length ∧
      ∀ t : List α, ChainBound t (C.fixedChainBudget (m + 1)) →
          NoSuffixOccurrenceEndsBetween (W i) t B c (W i).length := by sorry
