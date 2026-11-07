-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_8_shifts_flip_one_bit
-- name    : ContractionLemma.lemma_A_8_shifts_flip_one_bit
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:25.86635+00:00
-- url     : https://prove2.me/theorems/7d08f68e-fa39-4ec0-84ec-9d3c8d422d53
-- title:
--   Lemma A.8 — shifts flip one bit
-- statement:
--   Let $t$ be a nonzero integer of level $i=v_2(t)$, and let $x,y$ be slots with $y=x+t$. Then $x$ and $y$ agree in every bit to the right of position $i$ and differ in bit $i$.
--
--   This is the arithmetic behind the orientation rule of the packing: all shifts of one level flip the same bit.
--
--   **Formalization Note** Bit $k$ of a slot is `Nat.testBit`, with bit $0$ the rightmost.
--
--   Differences from the source: none.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.8, p.58; proof p.84

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

/-- **Lemma A.8 (Shifts flip one bit)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.58 (PDF p.61); proof p.84.

Let `t` be a nonzero integer of level `i = v₂(t)`, and let `x, y` be slots (in
`{0, …, 2^a − 1}`) with `y = x + t`. Then `x` and `y` agree in every bit to the right of
position `i` and differ in bit `i`.

**Formalization Note.** Bit `k` of a slot is `Nat.testBit · k` (bit `0` is the rightmost);
the level is `padicValInt 2 t`. -/
theorem lemma_A_8_shifts_flip_one_bit (a : ℕ) (t : ℤ) (ht : t ≠ 0) (x y : ℕ)
    (hx : x < 2 ^ a) (hy : y < 2 ^ a) (hxy : (y : ℤ) = x + t) :
    (∀ k < padicValInt 2 t, x.testBit k = y.testBit k) ∧
      x.testBit (padicValInt 2 t) ≠ y.testBit (padicValInt 2 t) := by sorry

end ContractionLemma
