-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_Supplement_theorem_8
-- name    : AutoQMem.Lindblad.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:47:23.693321+00:00
-- url     : https://prove2.me/theorems/aadf26c3-c40d-493e-9eaa-92cd3153b290
-- title:
--   Theorem 8: for syndrome-based channels, sector processes that $q_X$-, $q_Z$-remember give a quantum $(q_X+q_Z)$-memory through round $m$, and conversely ($\epsilon$ to $\epsilon$)
-- statement:
--   Consider an $n$-qubit CSS code with a designated logical qubit (encoding unitary $U$, bare logicals $\bar X=X^{\ell_X}$, $\bar Z=Z^{\ell_Z}$), readout decoders $\mathrm{Dec}_X,\mathrm{Dec}_Z$ with logical-error indicators $b_X,b_Z$, and a syndrome-based quantum channel $Q_*$ with induced X- and Z-sector chains (one-step matrices $B_X,B_Z$). For a stored codeword $w_0\in C_X$, write
--   $$\Pr\big[b_X(\xi^{(X)}_r)\neq b_X(\xi^{(X)}_0)\big]=\sum_{y}B_X^r(w_0,y)\,\big[b_X(y\oplus w_0)\neq b_X(0)\big]$$
--   for the error process $\xi^{(X)}_r=\chi^{(X)}_r\oplus w_0$ of the chain started at $w_0$, and similarly for Z. For every $m\in\mathbb N$ and all real $q_X,q_Z,\epsilon$:
--
--   1. if, for some stored codewords $w^X_0\in C_X$, $w^Z_0\in C_Z$, the X- and Z-sector processes $q_X$- and $q_Z$-remember $b_X,b_Z$ through round $m$, then
--   $$F_{\min}[Q_*^r]\ \ge\ 1-(q_X+q_Z)\qquad\text{for every }0\le r\le m ;$$
--   2. if $F_{\min}[Q_*^r]\ge1-\epsilon$ for every $0\le r\le m$, then for every stored codeword each sector process $\epsilon$-remembers its logical-error indicator through round $m$.
--
--   This is the synchronous (discrete-time) counterpart of the published Theorem 1: under any syndrome-based channel, quantum memory of the designated logical qubit is equivalent, up to a factor two in the error, to memory of the two induced classical sector chains.
--
--   Differences from the source:
--   - encoding: n-qubit CSS code with a designated logical qubit (Definitions 2.1, 2.8–2.9) → n = n'+1 qubits, the designated qubit is qubit 0, and the conjugate-pair facts H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X·ℓ_Z = 1 are explicit (the base mission's LogicalQubit); reason: the encoding unitary is arbitrary, so naming qubit 0 loses no generality; same instances
--   - encoding: a CPTP map that admits a syndrome-based Kraus representation (Definition 2.35) → the theorem quantifies over the Kraus data K and uses the channel K.apply; reason: every syndrome-based channel has such data, and the sector chains (Definition 2.36) are defined from it
--   - reading: Pr[b_σ(ξ_r) ≠ b_σ(ξ_0)] for the induced error process ξ_r = χ_r ⊕ w_0 → Σ_y (B_σ^r)(w_0, y)[b_σ(y + w_0) ≠ b_σ(0)] (the base flipProb at M a = B_σ^⌊a⌋₊), with the stored codeword explicit: assumed for one stored pair in (i), concluded for every stored codeword in (ii); reason: Reading R2 of the base mission; the law of the error process does not depend on w_0 (p. 27), so the strongest form is taken in each direction
--   - encoding: inf over r ∈ {0,…,m} of F_min[Q_*^r] and sup over r of the flip probability → pointwise bounds for every r ≤ m; reason: equivalent on a finite index set
--   - encoding: p_X(u | s) = P^(X)_u(s), the syndrome eigenvalue → the real part of Tr(P^(X)_u Π^X_s)/Tr(Π^X_s) (base eigX), evaluated at s = H_X e; reason: equal to the eigenvalue at valid syndromes, which are the only ones used; the eigenvalue is real there
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Theorem 8, p. 30 (PDF p. 32); proof §5.3, p. 45 (PDF p. 47)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_SyndromeChannel
import Definitions.Def_AutoQMem_Lindblad_Supplement_IsQuantumMemoryThrough
import Definitions.Def_AutoQMem_Lindblad_flipProb
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Theorem 8 (Quantum–classical memory equivalence for syndrome-based channels).** Drechsler, Oreg,
Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of
2026-11-03), Theorem 8, p. 30 (PDF 32); proof §5.3, p. 45 (PDF 47).

Consider a CSS code with a designated logical qubit evolving under a syndrome-based quantum channel
`Q_*`, with induced sector error processes `ξ^{(X)}_r`, `ξ^{(Z)}_r`.
1. If the X- and Z-sector processes respectively `q_X`- and `q_Z`-remember their logical-error
   indicators `b_X` and `b_Z` through round `m`, then the encoded system is a quantum
   `(q_X + q_Z)`-memory through round `m`.
2. Conversely, if the encoded system is a quantum `ε`-memory through round `m`, then each induced
   sector process `ε`-remembers its logical-error indicator through round `m`.

**Formalization Note.**
* Every CSS code (`n = n' + 1 ≥ 1`, dependent rows allowed), every designated logical qubit, every
  pair of readout decoders, every syndrome-based Kraus family `K` (Definition 2.35), every
  `m : ℕ`, all real `q_X, q_Z, ε`. The physical channel after `r` rounds is `Q_*^r` (eq. (70)),
  `K.apply^[r]`, with `r = 0` the identity.
* The induced sector chains have one-step matrices `B_X = K.BX`, `B_Z = K.BZ` (Definition 2.36);
  `Pr[b(ξ_r) ≠ b(ξ_0)]` is the base `flipProb` applied to `a ↦ B^{⌊a⌋₊}` at `a = r`, i.e.
  `Σ_y (B^r)(w_0, y) [b(y + w_0) ≠ b(0)]` (Reading R2: the chain starts at the stored codeword
  `w_0` and `ξ_r = χ_r ⊕ w_0`, eq. (69)). In (i) remembering is assumed for one stored pair; in (ii)
  it is concluded for every stored codeword. -/
theorem theorem_8 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C)
    (DX : Decoder C.HX) (DZ : Decoder C.HZ) {ι : Type} [Fintype ι] (K : SyndromeChannel C ι)
    (m : ℕ) (qX qZ ε : ℝ) :
    (∀ w0X ∈ C.codeX, ∀ w0Z ∈ C.codeZ,
      RemembersThrough (fun r : ℕ => flipProb (fun a => K.BX ^ ⌊a⌋₊) C.HX Q.lX DX w0X r) m qX →
      RemembersThrough (fun r : ℕ => flipProb (fun a => K.BZ ^ ⌊a⌋₊) C.HZ Q.lZ DZ w0Z r) m qZ →
      IsQuantumMemoryThrough Q DX DZ (fun r => K.apply^[r]) m (qX + qZ)) ∧
    (IsQuantumMemoryThrough Q DX DZ (fun r => K.apply^[r]) m ε →
      (∀ w0X ∈ C.codeX,
        RemembersThrough (fun r : ℕ => flipProb (fun a => K.BX ^ ⌊a⌋₊) C.HX Q.lX DX w0X r) m ε) ∧
      (∀ w0Z ∈ C.codeZ,
        RemembersThrough (fun r : ℕ => flipProb (fun a => K.BZ ^ ⌊a⌋₊) C.HZ Q.lZ DZ w0Z r) m ε)) := by sorry

end AutoQMem.Lindblad.Supplement
