-- Prove2me | Theorems.Thm_DepthOptQC_Synth_gqacf_to_wide
-- name    : DepthOptQC.Synth.gqacf_to_wide
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:24.6521+00:00
-- url     : https://prove2.me/theorems/96a7a67d-d622-4eae-929e-9ae82e0fc6be
-- title:
--   Theorem 1's gate set, step (b) — exact compilation of $G_{\mathrm{QACf}}$ into $\{H,S\}$ with Fan-Out and generalized Toffoli
-- statement:
--   There is a constant $C$ such that for all width bounds $w_F,w_T$, at least one of them positive, every layered circuit over $G_{\mathrm{QACf}}$ (with Fan-Out of at most $w_F$ targets and generalized Toffoli of at most $w_T$ controls) on $n$ wires can be replaced by a layered circuit over $\{H,S\}$ together with the same Fan-Out and generalized Toffoli gates, on the same $n$ wires, implementing exactly the same unitary, with
--   $$
--   \operatorname{depth}\le C\cdot\operatorname{depth}(C_{\mathrm{orig}}),\qquad \operatorname{size}\le C\cdot\operatorname{size}(C_{\mathrm{orig}}).
--   $$
--   No ancilla is added and no global phase is allowed.
--
--   The paper states (§1.1) that its single-qubit synthesis constructions "require only $H$ and $S=T^2$ as single-qubit primitives, provided Toffoli gates remain available", and Theorem 1 states the constant-depth synthesizer over $H$ and $S$ with Fan-Out and generalized Toffoli, while Corollary 1 is stated over $G_{\mathrm{QACf}}$. This unnumbered step connects the two.
--
--   Differences from the source:
--   - reading: "our single-qubit synthesis constructions … require only H and S = T² as single-qubit primitives, provided Toffoli gates remain available" (p.5) and Theorem 1's gate set → an exact, ancilla-free, phase-free compilation of every G_QACf(wF, wT) layered circuit into a wideGateSet(wF, wT) layered circuit on the same wires, with depth and size at most C times; reason: reading R2: the paper passes from Corollary 1's gate set to Theorem 1's without a numbered statement; this is the precise form of that step
--   - encoding: "provided Toffoli gates remain available" → the hypothesis 1 ≤ wF ∨ 1 ≤ wT; reason: it only excludes the degenerate case where the target set has no two-qubit gate and CNOT cannot be built
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 1, p.6, and §1.1, p.5 (unnumbered compilation step)

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_gqacfGateSet
import Definitions.Def_DepthOptQC_Synth_wideGateSet

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Exact compilation of `G_QACf` into `{H, S}` with Fan-Out and generalized Toffoli**
(Vasconcelos, *Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Theorem 1, p.6; §1.1, p.5: "our
single-qubit synthesis constructions and depth-preserving QAC compiler require only H and `S = T²`
as single-qubit primitives, provided Toffoli gates remain available"; unnumbered). There is a
constant `C` such that for all width bounds `wF, wT` with at least one of them positive, every layered
circuit over `G_QACf` with those widths on `n` wires has a layered circuit over `{H, S}` with the
same Fan-Out and generalized Toffoli gates, on the same wires, implementing exactly the same unitary,
with at most `C` times the depth and `C` times the size.

**Formalization Note.** The step that turns Corollary 1's gate set into Theorem 1's (reading R2).
Exact equality of unitaries. The hypothesis `1 ≤ wF ∨ 1 ≤ wT` makes a CNOT (Fan-Out with one
target, or Toffoli with one control) available; without it the target set `{H, S}` has no two-qubit
gate. -/
theorem gqacf_to_wide :
    ∃ C : ℕ, ∀ (n wF wT : ℕ), (1 ≤ wF ∨ 1 ≤ wT) → ∀ c : LayeredCircuit (gqacfGateSet wF wT) n,
      ∃ c' : LayeredCircuit (wideGateSet wF wT) n,
        c'.unitary = c.unitary ∧ c'.depth ≤ C * c.depth ∧ c'.size ≤ C * c.size := by sorry

end DepthOptQC.Synth
