-- Prove2me | Theorems.Thm_DepthOneQExp_Supplement_theorem_2_17
-- name    : DepthOneQExp.Supplement.theorem_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:36:00.113728+00:00
-- url     : https://prove2.me/theorems/63204059-f94f-478b-a20f-b80e7118ff75
-- title:
--   Theorem 2.17 — 25 depth-1 Clifford+$T$ circuits form an expander on $\mathrm{SU}(2^{3s})$ with a uniform spectral gap
-- statement:
--   Let $T = e^{-i\pi Z/8} = \mathrm{diag}(e^{-i\pi/8}, e^{i\pi/8})\in\mathrm{SU}(2)$. There are a constant $\Delta>0$ and a range $r\in\mathbb N$ such that for every integer $s\ge1$, with $n = 3s$, there exist
--   $$
--   \mathcal V(n) = \{V_1,\dots,V_{25}\}\subset \mathrm{SU}(2^n)
--   $$
--   with the following properties:
--
--   1. $V_1 = T\otimes I_{n-1}$ and $V_2 = T^\dagger\otimes I_{n-1}$ ($T$, resp. $T^\dagger$, on the first qubit);
--   2. every other $V_i$ ($3\le i\le 25$) is a depth-1 1D Clifford circuit: a single layer of gates on pairwise disjoint qubits, each gate either a single-qubit gate in $\langle H,S\rangle$ or a CNOT, and every gate acts on qubits at cyclic distance at most $r$ on the ring of $n$ qubits;
--   3. $V_1,\dots,V_{25}$ is an expander on $\mathrm{SU}(2^n)$ with spectral gap $\Delta$: for every finite-dimensional unitary representation $\rho$ of $\mathrm{SU}(2^n)$ and every vector $|X\rangle$ orthogonal to the invariant subspace of $\rho$,
--   $$
--   \Bigl\|\frac1{25}\sum_{i=1}^{25}\rho(V_i)\,|X\rangle\Bigr\| \le (1-\Delta)\,\||X\rangle\|.
--   $$
--
--   The gap $\Delta$ and the range $r$ do not depend on $s$. This is what "uniformly bounded spectral gap" and "1D" mean: the sets $\mathcal V(3s)$ form an expander family of degree 25 on the special unitary groups $\mathrm{SU}(2^{3s})$, each generator a single layer of nearest-neighbour-type gates with exactly two non-Clifford generators. Compared with Theorem 2.2, which gives a gap only in the representation $U\otimes\bar U$, the gap here holds in every representation.
--
--   **Formalization Note** $\mathrm{SU}(2^n)$ is `Matrix.specialUnitaryGroup` on $n$-bit strings. $T\otimes I_{n-1}$ is the $T$ gate placed on qubit $0$ (the paper's qubit 1) via `MITMSynthesis.Placement.unitary`. The paper's $V_1, V_2, V_3,\dots$ are `V 0`, `V 1`, `V 2`, …. For $i\ge 2$ the matrix of the layer $L$ (`MITMSynthesis.layerUnitary L`) equals the underlying matrix of `V i`. The expander property is `IsUnitaryGroupExpander` (Definition 1.3), which includes $\Delta>0$.
--
--   Differences from the source:
--   - reading: "with a uniformly bounded spectral gap" → one $\Delta>0$ chosen before $s$; reason: Definition 1.3's expander family (same degree and same $\Delta$ in every dimension), which "uniformly" refers to.
--   - reading: "depth-1 1D … circuit" → a single layer on the ring of $3s$ qubits in which every gate's qubits are at cyclic distance $\le r$, with $r$ chosen before $s$; reason: the paper's expanders live on a 1D ring (§4, p.27) with constant-range generators (p.2).
--   - reading: "Clifford circuit" → gates from {single-qubit gates in $\langle H,S\rangle$} ∪ {CNOT}; reason: these are the generators of $\mathrm{Cl}(n)$ in Eq. (2.55), and the paper's generators use only $I, H, S, Z, S^\dagger$ and CNOT.
--   - reading: "an explicit expander" → existence of $V$; reason: explicitness has no Lean content.
--   - reading: "all finite dimensional unitary representations" → the continuous ones (`ConstGapCircuits.UnitaryRep`); reason: every finite-dimensional unitary representation of $\mathrm{SU}(d)$ is automatically continuous (van der Waerden), so it is the same class.
--   - encoding: $s\in\mathbb N$ → $1\le s$; reason: the paper's $\mathbb N$ starts at 1 (Theorem 2.2: "any integer $s\geqslant1$"); for $n=0$ there is no first qubit and $T\otimes I_{n-1}$ is undefined.
--   - encoding: the set $\{V_1,\dots,V_{25}\}$ → an indexed family `Fin 25 → SU(2^n)`, 0-based; reason: the average is over 25 generators with multiplicity, as in the base mission's Theorem 2.2.
--   - encoding: $T\otimes I_{n-1}$, $T^\dagger\otimes I_{n-1}$ → `Placement.unitary` of `tGate` / `tGate.inv` on qubit 0; reason: the same matrix in the base mission's gate framework.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.17, Eq. (2.54), p.15 (Definition 1.3, p.2; proof pp.15–17)

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_DepthOneQExp_Supplement_tGate
import Definitions.Def_DepthOneQExp_Supplement_cliffordGateSet
import Definitions.Def_DepthOneQExp_Supplement_IsRingLocalLayer
import Definitions.Def_DepthOneQExp_Supplement_IsUnitaryGroupExpander

namespace DepthOneQExp.Supplement

/-- **Theorem 2.17** (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary
group and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Theorem 2.17,
Eq. (2.54), p.15): let `n = 3s` with `s ∈ ℕ`. There exists an explicit expander
`V(n) = {V_1, …, V_25} ⊂ SU(2ⁿ)` on the unitary group such that `V_1 = T ⊗ I_{n−1}`,
`V_2 = T† ⊗ I_{n−1}` and every other `V_i` is a depth-1 1D Clifford circuit, with a uniformly bounded
spectral gap.

**Formalization Note** "Uniformly bounded spectral gap" is one `Δ > 0` (Definition 1.3,
`IsUnitaryGroupExpander`) chosen before `s`; "1D" is one range `r` on the ring of `3s` qubits, also
chosen before `s` (`IsRingLocalLayer`). `T = e^{−iπZ/8} = diag(e^{−iπ/8}, e^{iπ/8})` (`tGate`, p.15)
and `T ⊗ I_{n−1}` is `T` placed on qubit `0` (the paper's qubit 1); `T†` is `tGate.inv`. The paper's
`V_1, V_2, V_3, …` are `V 0, V 1, V 2, …`. A depth-1 Clifford circuit is a layer of single-qubit gates
from `⟨H, S⟩` and CNOTs on pairwise disjoint qubits (`cliffordGateSet`); its matrix
`MITMSynthesis.layerUnitary L` is the underlying matrix of `V i`, so it lies in `SU(2ⁿ)`. "Explicit"
has no Lean content; the statement is existential in `V`. The family is indexed by `Fin 25`. -/
theorem theorem_2_17 :
    ∃ Δ : ℝ, ∃ r : ℕ, ∀ s : ℕ, ∀ hs : 1 ≤ s,
      ∃ V : Fin 25 → Matrix.specialUnitaryGroup (MITMSynthesis.Q (3 * s)) ℂ,
        ((V 0 : Matrix (MITMSynthesis.Q (3 * s)) (MITMSynthesis.Q (3 * s)) ℂ) =
            MITMSynthesis.Placement.unitary
              ⟨tGate, Fin.castLEEmb (show 1 ≤ 3 * s by omega)⟩) ∧
        ((V 1 : Matrix (MITMSynthesis.Q (3 * s)) (MITMSynthesis.Q (3 * s)) ℂ) =
            MITMSynthesis.Placement.unitary
              ⟨tGate.inv, Fin.castLEEmb (show 1 ≤ 3 * s by omega)⟩) ∧
        (∀ i : Fin 25, 2 ≤ i.val →
          ∃ L : List (MITMSynthesis.Placement (3 * s)),
            IsRingLocalLayer (3 * s) r cliffordGateSet L ∧
              MITMSynthesis.layerUnitary L =
                (V i : Matrix (MITMSynthesis.Q (3 * s)) (MITMSynthesis.Q (3 * s)) ℂ)) ∧
        IsUnitaryGroupExpander V Δ := by sorry

end DepthOneQExp.Supplement
