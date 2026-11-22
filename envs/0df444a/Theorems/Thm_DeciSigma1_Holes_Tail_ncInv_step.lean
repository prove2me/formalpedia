-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_ncInv_step
-- name    : DeciSigma1.Holes.Tail.ncInv_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:42.391469+00:00
-- url     : https://prove2.me/theorems/7f14ee49-dec2-4992-ad64-06ce4cff91e5
-- title:
--   Tail: nc Inv step
-- statement:
--   The Tail construction uses the nc Inv step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L244-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L244-L269

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
variable {ι : Type} [Fintype S]
variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)
variable {M st Ω J v}
omit [Fintype ι]
omit [DecidableEq ι]

theorem DeciSigma1.Holes.Tail.ncInv_step (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u)) {h x : ι}
    (hhx : h ≠ x) {a b : ℕ} (hb : b ≤ J x) (heq : ∀ t, (Ω h).stream (a + t) = (Ω x).stream (b + t))
    (hx : CandidateInvariant Ω J v x) : CandidateInvariant Ω J v h ∧ h ≠ v := by sorry
