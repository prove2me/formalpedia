-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_7_shift_curve
-- name    : ContractionLemma.lemma_A_7_shift_curve
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:08.998797+00:00
-- url     : https://prove2.me/theorems/26604be4-286a-4e3f-ba0e-1e923548d8ad
-- title:
--   Lemma A.7 — the shift curve passes through the scaled shifts
-- statement:
--   For every placement of the edges into packets of $L=2^a$ slots, the shift curve $W(T)$ satisfies:
--
--   1. $W(t)=c_t\sigma_t$ for every grid point $t\in S$, where $c_t=C'(t)/C'(0)\ne 0$;
--   2. $W(0)=I$;
--   3. every entry of $W(T)$ has degree at most $2L-1$.
--
--   Hence the rewiring polynomial has degree at most $M(2L-1)$ and equals the contraction at $T=0$.
--
--   Differences from the source: none.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.7, p.58; proof p.83

import Mathlib
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_Placement

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.7 (The shift curve)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.58 (PDF p.61); proof p.83.

For every placement of the edges into packets of `L = 2^a` slots, the shift curve `W(T)`
satisfies:
(a) `W(t) = c_t σ_t` for every grid point `t ∈ S`, where `c_t = C′(t)/C′(0) ≠ 0`;
(b) `W(0) = I`;
(c) every entry of `W(T)` has degree at most `2L − 1`. -/
theorem lemma_A_7_shift_curve {E : Type*} [DecidableEq E] (a : ℕ) (pl : Placement E a) :
    (∀ t ∈ gridS a, (pl.wiring.map fun p => p.eval (t : ℚ)) = shiftConst a t • pl.shiftMat t ∧
      shiftConst a t ≠ 0) ∧
    (pl.wiring.map fun p => p.eval 0) = 1 ∧
    (∀ e f, (pl.wiring e f).natDegree ≤ 2 * 2 ^ a - 1) := by sorry

end ContractionLemma
