-- Prove2me | Theorems.Thm_FixpReciprocal_lemma_4_1
-- name    : FixpReciprocal.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:08.517016+00:00
-- url     : https://prove2.me/theorems/3a3798fb-9572-49f4-a80c-f4310d4b4900
-- title:
--   Lemma 4.1 — squaring with a reciprocal: four clipped affine gates and three $R_\tau$ gates
-- statement:
--   For every rational $\tau>0$, the squaring function $x\mapsto x^2$ on $[0,1]$ can be computed exactly by an acyclic circuit consisting of four clipped affine gates and three $R_\tau$ gates. The number of gates is independent of $\tau$, and the circuit can be constructed in time polynomial in the bit length of $\tau$.
--
--   The circuit is the explicit seven-gate circuit of the proof. For every $x\in[0,1]$, its output wire equals $x^2$ and every wire value lies in $[0,1]$. This is the only nonlinear step of the main theorem.
--
--   Differences from the source:
--
--   - generalization: the circuit computes x² exactly → the explicit circuit of the proof computes x² exactly, and every wire value lies in [0, 1]; reason: the sentence before the lemma promises the wire bound, and the explicit circuit gives the lemma's existential statement
--   - reading: constructible in time polynomial in the bit length of τ → a TM2 machine with τ as input, encRat to encRGates; reason: the paper names no machine model
--   - generalization: the circuit is constructed in polynomial time for every rational τ > 0 → one machine computes squareCircuit τ for every rational τ, including τ ≤ 0; reason: squareCircuit is a total formula in τ (Lean's q / 0 = 0 at τ = 0), so the same arithmetic serves τ ≤ 0, and restricting the machine to τ > 0 gives the source's clause
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Lemma 4.1, p.11 (PDF p.13); proof, p.12 (PDF p.14); "while keeping every intermediate value in [0, 1]", §4.1, p.11

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_FixpReciprocal_RGate
import Definitions.Def_FixpReciprocal_squareCircuit

namespace FixpReciprocal

/-- **Lemma 4.1 (Squaring with a reciprocal).** For every rational `τ > 0`, the squaring function `x ↦ x²` on
`[0, 1]` can be computed exactly by an acyclic circuit consisting of four clipped affine gates and three `R_τ`
gates. The number of gates is independent of `τ`, and the circuit can be constructed in time polynomial in the
bit length of `τ`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Lemma 4.1, p.11; proof, p.12; "keeping every intermediate value in `[0, 1]`", §4.1, p.11.

**Formalization Note.** The circuit is the explicit `squareCircuit τ` of the proof. Its construction takes `τ`
as machine input, uniformly. -/
theorem lemma_4_1 :
    Nonempty (Turing.TM2ComputableInPolyTime OnlineCRS.Combine.encRat encRGates squareCircuit) ∧
    ∀ τ : ℚ, 0 < τ →
      (squareCircuit τ).length = 7 ∧
      (squareCircuit τ).countP RGate.isAff = 4 ∧
      (squareCircuit τ).countP RGate.isRecip = 3 ∧
      StraightLine (squareCircuit τ) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (∀ w ∈ seqWires τ (squareCircuit τ) x, w ∈ Set.Icc (0 : ℝ) 1) ∧
        (seqWires τ (squareCircuit τ) x).getLast? = some (x ^ 2) := by sorry

end FixpReciprocal
