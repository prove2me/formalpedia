-- Prove2me | Theorems.Thm_DepthOptQC_Synth_gqnc_to_htcx
-- name    : DepthOptQC.Synth.gqnc_to_htcx
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:03.101686+00:00
-- url     : https://prove2.me/theorems/587e94ca-d2f0-40e1-bf5d-c2d9ac4dbc16
-- title:
--   Theorem 1's gate set, step (a) — exact compilation of $G_{\mathrm{QNC}}$ into $\{H,T,\mathrm{CNOT}\}$ with constant-factor depth and size
-- statement:
--   There is a constant $C$ such that every layered circuit over $G_{\mathrm{QNC}}=\{H,X,Z,S,S^\dagger,\mathrm{CNOT},CZ,\mathrm{Toffoli}\}$ on $n$ wires can be replaced by a layered circuit over $\{H,T,\mathrm{CNOT}\}$ on the same $n$ wires that implements exactly the same unitary, with
--   $$
--   \operatorname{depth}\le C\cdot\operatorname{depth}(C_{\mathrm{orig}}),\qquad \operatorname{size}\le C\cdot\operatorname{size}(C_{\mathrm{orig}}).
--   $$
--   No ancilla is added and no global phase is allowed.
--
--   The paper uses this step without numbering it: Theorem 8 is stated over $G_{\mathrm{QNC}}$, while Theorem 1 states the bounded-width synthesizer over $\{H,T,\mathrm{CNOT}\}$, and §3.2.1 notes that "standard Clifford+T decompositions give the same asymptotic bounds". It is what makes the first clause of Theorem 1 follow from Theorem 8 and Lemma 6.
--
--   Differences from the source:
--   - reading: Theorem 1's "circuit over {H, T, CNOT}" and "Standard Clifford+T decompositions give the same asymptotic bounds over {H, T, CZ}" (p.16) → an exact, ancilla-free, phase-free compilation of every G_QNC layered circuit into an {H, T, CNOT} layered circuit on the same wires, with depth and size at most C times; reason: reading R2: the paper passes from Theorem 8's gate set to Theorem 1's without a numbered statement; exact gate-by-gate substitution with constant overhead is the content of a standard Clifford+T decomposition; Lean uses Theorem 1's {H, T, CNOT}
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 1, p.6, and §3.2.1, p.16 (unnumbered compilation step)

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_gqncGateSet
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Exact compilation of `G_QNC` into `{H, T, CNOT}`** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Theorem 1, p.6, "a depth-`O(log log(1/ε))` circuit over
`{H, T, CNOT}`"; §3.2.1, p.16, "Standard Clifford+T decompositions give the same asymptotic bounds";
unnumbered). There is a constant `C` such that every layered circuit over
`G_QNC = {H, X, Z, S, S†, CNOT, CZ, Toffoli}` on `n` wires has a layered circuit over `{H, T, CNOT}`
on the same `n` wires implementing exactly the same unitary (no ancilla, no phase), with at most `C`
times the depth and `C` times the size.

**Formalization Note.** This is the step that turns Theorem 8's gate set into Theorem 1's (reading
R2). The equality of unitaries is exact. -/
theorem gqnc_to_htcx :
    ∃ C : ℕ, ∀ (n : ℕ) (c : LayeredCircuit gqncGateSet n),
      ∃ c' : LayeredCircuit htcxGateSet n,
        c'.unitary = c.unitary ∧ c'.depth ≤ C * c.depth ∧ c'.size ≤ C * c.size := by sorry

end DepthOptQC.Synth
