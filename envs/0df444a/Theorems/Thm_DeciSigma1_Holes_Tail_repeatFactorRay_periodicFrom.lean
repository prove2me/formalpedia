-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_periodicFrom
-- name    : DeciSigma1.Holes.Tail.repeatFactorRay_periodicFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:35.566491+00:00
-- url     : https://prove2.me/theorems/9341a16c-72dc-43b5-b834-d9ce5881db0b
-- title:
--   Tail: repeat Factor Ray periodic From
-- statement:
--   A period `p ∣ c' - c` of the closure region `[c - B, c')` is a period of the ray from
--   `c - B` on.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L96-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L96-L128

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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}

theorem DeciSigma1.Holes.Tail.repeatFactorRay_periodicFrom (hcl : ClosedAt T q0 x B c c') {p : ℕ}
    (hp : 0 < p)
    (hdvd : p ∣ c' - c) (hper : PeriodicOn x p (c - B) c') :
    PeriodicFrom (repeatFactorRay x c c' hcl.2.1 hcl.2.2.1).stream (c - B) p := by sorry
