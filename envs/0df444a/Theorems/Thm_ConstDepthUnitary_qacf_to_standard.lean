-- Prove2me | Theorems.Thm_ConstDepthUnitary_qacf_to_standard
-- name    : ConstDepthUnitary.qacf_to_standard
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:54.143984+00:00
-- url     : https://prove2.me/theorems/6c3c22d4-5e70-4adf-bdca-9afb3676e87e
-- title:
--   §3.1 — fan-out gates recompile to one- and two-qubit gates with no ancillas
-- statement:
--   There is a universal constant $C$ such that every circuit $D$ with fan-out on a finite set of wires $W$ has a circuit $D'$ of one- and two-qubit gates on the same wires, with the same matrix, of depth
--   $$\operatorname{depth}(D')\le C\cdot\operatorname{depth}(D)\cdot\lceil\log_2(|W|+1)\rceil.$$
--   No extra wires are used.
--
--   Differences from the source:
--   - reading: "depth-(d log(n+m))" with no O → depth O(d log(n + m)); reason: one fan-out on three qubits already needs depth 2 > log₂ 3; the same paragraph says O(log ℓ) per fan-out
--   - encoding: log(n + m) for n + m wires → ⌈log₂(|W| + 1)⌉, for any finite W; reason: it stays positive at one wire
--   - reading: a depth-d QACf circuit for U yields a standard-model circuit for U → every circuit D on W has a standard circuit D′ on the same wires with D′.matrix = D.matrix; reason: the paragraph's construction replaces each fan-out gate exactly, and an equal matrix preserves every implementation property, so it gives the printed claim for every U
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.1, p.14

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit

namespace ConstDepthUnitary

/-- §3.1: fan-out recompilation. A depth-`d` circuit on the wires `W` is exactly the same operator as a circuit of one- and
two-qubit gates on the same wires (no extra ancillae), of depth `O(d log |W|)`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.1, p.14 (unnumbered claim).

**Formalization Note** The printed "depth-(d log(n+m))" has no `O`; it is read as `O(d log(n + m))`, since one fan-out on three
qubits already needs depth 2 > log₂ 3. `Nat.clog 2 (|W| + 1)` keeps the bound positive at `|W| = 1`. -/
theorem qacf_to_standard :
    ∃ C : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (D : Circuit W),
      ∃ D' : Circuit W, D'.IsStandard ∧ D'.matrix = D.matrix ∧
        D'.depth ≤ C * D.depth * Nat.clog 2 (Fintype.card W + 1) := by sorry

end ConstDepthUnitary
