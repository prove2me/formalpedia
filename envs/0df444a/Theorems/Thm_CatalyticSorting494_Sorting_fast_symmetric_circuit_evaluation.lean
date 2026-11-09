-- Prove2me | Theorems.Thm_CatalyticSorting494_Sorting_fast_symmetric_circuit_evaluation
-- name    : CatalyticSorting494.Sorting.fast_symmetric_circuit_evaluation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:18.63613+00:00
-- url     : https://prove2.me/theorems/9b030d40-ac5e-4246-9517-419a0828b97a
-- title:
--   Theorem 1.1 — catalytic evaluation of d-layer, w-wire symmetric circuits in Õ(w2^d) time and O(log w + d) clean space
-- statement:
--   Let $C$ be a well-formed circuit of symmetric gates with $d$ layers and size $w$, and let $x$ be an input to it. There is one catalytic machine $M$, one capacity function $c(w,d)$, and constants $A,k$, all fixed before $C$, $x$ and the catalytic content, with the following property. Write
--   $$T=(w+1)\,2^{d}.$$
--   Then $c(w,d)\le A\,T\,(\log_2(T+2))^{k}$, and for every initial catalytic content $z\in\{0,1\}^{c(w,d)}$, the machine started on the encoding of $(C,x)$ halts within
--   $$A\,T\,(\log_2(T+2))^{k}\ \text{ steps, using at most }\ A\,\big(\lfloor\log_2(w+2)\rfloor+d\big)\ \text{ clean bits,}$$
--   with the whole output $C(x)$ XORed into the initial segment of the catalytic tape and every other catalytic bit restored.
--
--   The gates are arbitrary symmetric functions of arbitrary fan-in, and the output may have many bits. The base of the exponential is $2$, so the running time is near-linear in $w$ whenever $d=o(\log w)$. This is the engine behind the mission's sorting goal.
--
--   Differences from the source:
--   - encoding: "w-wire" → `wireCount`, adding one wire per input bit, gate and output; reason: same order of magnitude on circuits with no unread input, no fan-in-zero gate and no repeated output, and the size is the only quantity that can pay for reading those objects otherwise.
--   - encoding: Õ(w2^d) and O(log(w) + d) → A·T·(log₂(T+2))^k with T=(w+1)2^d, and A·(⌊log₂(w+2)⌋+d); reason: the shifts change nothing beyond a constant factor for w ≥ 1 and keep the bounds meaningful at w = 0, where the header must still be read.
--   - encoding: "takes in a circuit" → the fixed binary format `SymCircuit.encode`; reason: the source names no format; a fixed one is needed so the input cannot carry the answer.
--   - reading: "catalytic algorithm" with unspecified dirty space → a capacity c(w,d) ≤ Õ(w2^d); reason: §2, printed p.7, says all the paper's algorithms have catalytic space at most the runtime up to polylogarithmic factors, and an unbounded catalyst is not what is claimed.
--   - reading: "RAM access" → a Turing machine with three binary index tapes, charging addresses as clean bits; reason: Definition 2.2 names a Turing machine with random-access heads, and this is the standard reading with the fewest free operations.
--   - generalization: positive circuit parameters under the source's convention ℕ={1,2,…} → also depth-zero and empty circuits, and fan-in-zero constant gates; reason: the positive-parameter source instances retain their full output and asymptotic bounds, while the augmented size and shifted logarithms give meaningful bounds on these additional finite cases.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Theorem 1.1, printed p.10 (PDF p.11); also printed p.3 (PDF p.4)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine
import Definitions.Def_CatalyticSorting494_Sorting_SymCircuit

namespace CatalyticSorting494.Sorting

/-- Theorem 1.1. One machine `M`, one catalytic capacity function `c` of the size and depth, and one
pair of constants `A, k` work for all circuits, inputs and initial catalytic contents. The factor
`C.wireCount + 1` equals `w` up to a factor of two when `w ≥ 1`, and covers the empty circuit. -/
theorem fast_symmetric_circuit_evaluation :
    ∃ (M : Machine) (c : ℕ → ℕ → ℕ) (A k : ℕ),
      ∀ (C : SymCircuit) (x : List Bool), C.WellFormed → x.length = C.numInputs →
        c C.wireCount C.depth ≤ softBound A k ((C.wireCount + 1) * 2 ^ C.depth) ∧
        ∀ z : List Bool, z.length = c C.wireCount C.depth →
          ComputesWithin M (C.encode x) z (C.eval x)
            (softBound A k ((C.wireCount + 1) * 2 ^ C.depth) : ℕ)
            (A * (Nat.log 2 (C.wireCount + 2) + C.depth)) := by sorry

end CatalyticSorting494.Sorting
