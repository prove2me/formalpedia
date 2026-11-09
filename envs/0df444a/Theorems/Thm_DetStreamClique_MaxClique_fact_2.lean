-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_fact_2
-- name    : DetStreamClique.MaxClique.fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:02:14.893206+00:00
-- url     : https://prove2.me/theorems/1525c264-1dc5-4a64-86d6-c2dd5b0d6414
-- title:
--   Fact 2 — information cost is bounded by communication
-- statement:
--   For any finite probability law, any finite-valued Alice input $X$, and any deterministic message function $f:X\to M$, suppose $|M|\le2^c$. Entropy and mutual information are in bits. Then
--   $$I(X;f(X))\le\log_2|M|,\qquad I(X;f(X))\le c.$$
--   The input may be any random variable on a finite probability space; Bob's input does not affect the message. This is the information-cost bound for one-way protocols.
--
--   Differences from the source:
--   - encoding: communication cost in bits → a finite message alphabet of cardinality at most 2^c, and its base-2 logarithm; reason: a fixed message alphabet is the paper model of a c-bit message; entropy is converted from nats to bits
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Fact 2, p. 8

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Information
import Definitions.Def_DetStreamClique_MaxClique_Machines

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Fact 2, p. 8, for any finite input law and deterministic message. -/
theorem fact_2 {Ω X M : Type} [Fintype Ω] [Fintype X] [Fintype M]
    (P : FiniteLaw Ω) (x : Ω → X) (send : X → M)
    (c : ℕ) (hbits : FitsBits M c) :
    mutualInformation P x (fun w => send (x w)) ≤ Real.logb 2 (Fintype.card M : ℝ) ∧
    mutualInformation P x (fun w => send (x w)) ≤ (c : ℝ) := by sorry

end DetStreamClique.MaxClique
