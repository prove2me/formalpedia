-- Prove2me | Theorems.Thm_ErrAmpOV_hardcode_random_string
-- name    : ErrAmpOV.hardcode_random_string
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:38.536758+00:00
-- url     : https://prove2.me/theorems/89722faa-f691-4c3f-9bdb-227d8bca59ae
-- title:
--   Hard-coding step (proof of Theorem 3.1, p.11) — a good random string gives a deterministic circuit
-- statement:
--   Let $f$ be a Boolean function on a finite set $\iota$ of input bits, and suppose $f$ is decided with zero error and error $\delta$ by a probabilistic circuit with at most $S$ gates. If
--   $$
--   2^{|\iota|}\cdot\delta<1,
--   $$
--   then a single random string $r^*$ is good for every input simultaneously, and hard-wiring it gives a deterministic circuit with at most $S+2$ gates that computes $f$ on every input.
--
--   This is the last step of the derandomization: Theorem 3.2 makes $\delta$ small enough to beat the $2^{2nd}$ inputs of OV.
--
--   Differences from the source:
--   - generalization: the step for OV_{n,d}: 2^{2nd} · 2^{−Ω(n^{1.25})} < 1, and size O(n^{2−α/4} · d^c) → any f on a finite input set ι and any δ with 2^{|ι|}·δ < 1; size ≤ S + 2 for any size bound S of the probabilistic circuit; reason: OV has |ι| = 2nd; the argument never uses the problem; S + 2 is at most the printed O-bound
--   - encoding: hard-code r* into the circuit → each random input is replaced by one of two constant gates, which is where +2 comes from; the abort wire is dropped; reason: the cost of hard-wiring in the ErrAmpOV.Circuit model
--   - encoding: Boolean circuits, no gate basis fixed, size = number of gates → ErrAmpOV.Circuit: constant, NOT, AND, OR gates of fan-in at most 2, unbounded fan-out, inputs not counted, a list of output wires; a read of a gate not yet computed returns false; reason: the basis is unspecified on the page; complete fan-in-2 bases differ by a constant factor, and the out-of-range read only gives a free constant false
--   - encoding: ⊥ is a separate output symbol (pp.5–6); Pr over r in {0,1}^{p(n)} → two output wires (abort, value); correct means output [false, f x], ⊥ means output [true, v]; the probability is a count of r : Fin p → Bool over 2^p, with p chosen with the circuit; reason: the page itself encodes ⊥ in output wires; same class up to the abort wire
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), hard-coding step, proof of Theorem 3.1, p.11

import Mathlib
import Definitions.Def_ErrAmpOV_SizeDecides
import Definitions.Def_ErrAmpOV_ZPDecides

set_option autoImplicit false

namespace ErrAmpOV

/-- Hard-coding a good random string (proof of Theorem 3.1, p.11). Let `f` be a Boolean
function on a finite set `ι` of input bits, decided with zero error and error `δ` by a
probabilistic circuit of size at most `S`. If `2^{|ι|}·δ < 1`, then some random string `r*` is
good for every input simultaneously, and hard-wiring it gives a deterministic circuit of size
at most `S + 2` that computes `f` on every input.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
proof of Theorem 3.1, p.11 ("`2^{2nd} · 2^{−Ω(n^{1.25})} < 1`. Thus, we can non-uniformly
hard-code a 'good' random string `r*` …").

**Formalization Note.** The page does this for `OV_{n,d}` with `|ι| = 2nd`; it is stated here
for every `f` and `δ` (a generalization). The `+ 2` is the cost of hard-wiring in the
`ErrAmpOV.Circuit` model: two constant gates (`false`, `true`) replace the random input wires. -/
theorem hardcode_random_string {ι : Type} [Fintype ι] (f : (ι → Bool) → Bool) (δ S : ℝ)
    (h : ZPDecides δ S f) (hδ : (2 : ℝ) ^ Fintype.card ι * δ < 1) :
    SizeDecides (S + 2) f := by sorry

end ErrAmpOV
