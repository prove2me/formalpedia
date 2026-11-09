-- Prove2me | Theorems.Thm_CodedSorting_lemma_5_1
-- name    : CodedSorting.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:52.327945+00:00
-- url     : https://prove2.me/theorems/a559c365-27d1-451a-8f7f-422f1528d6eb
-- title:
--   Lemma 5.1 — the local circuit on 111 data pairs and 439 auxiliary registers in $\mathbb Q^8$
-- statement:
--   Let $v=111$, $R=439$ and let $E=\mathbb Q^8$ carry the standard inner product. There exist one-dimensional rational subspaces $\ell_t\subseteq E$ ($t\in[v]$), a permutation $\pi$ of $[v]$, and a binary linear circuit on $v$ pairs of data registers $x=(x_t)$, $y=(y_t)$ and $R$ auxiliary registers $z=(z_r)$, $2v+R=661$ registers in total, with nine temporary wires and subspace labels in $E$, such that
--
--   1. the circuit implements
--   $$(x,y,z)\longmapsto(x,\;y+x,\;z)$$
--   over $\mathbb F_2$, for every initial state;
--   2. the labels grow by inclusion along every main wire, and temporary-wire edges have nested endpoints;
--   3. the input and output labels are $x_t:\ \ell_t\to E$, $y_t:\ 0\to\ell_t^{\perp}$, $z_r:\ 0\to E$;
--   4. each temporary wire branches from a register node with a seven-dimensional label, its copy is read only by zero-labeled gates, and meanwhile the original register keeps its value and its label;
--   5. the temporary wires have total dimension difference $c=9\times7=63$;
--   6. $\ell_t\perp\ell_{\pi(t)}$ for every $t\in[v]$.
--
--   This local circuit is the building block of the global circuit of Lemmas 5.2–5.3: each of its invocations performs one of the three XOR updates of a data exchange, at temporary-wire cost $63$ for $111$ data pairs.
--
--   **Formalization Note** The circuit is the one of [eum26, Dre26]; the paper checks it by computation and does not print it.
--
--   Differences from the source:
--   - encoding: a finite binary linear circuit with temporary wires and node labels (§4.2, §5) → `XorCircuit` (gates target ← target + Σ register operands + Σ copies over $\mathbb F_2$; copies branch at a node of their register and are read only later), `Node`, wires and `LabeledCircuit` with one label per node; reason: the paper's circuit and network written out; one label per gate node is "all participating registers have the same subspace label"
--   - reading: "changes the copy's label to zero, and then connects the zero-labeled XOR gates that use the copy … the wire terminates after its last use" → every gate reading a copy has label $0$, and every copy is read by at least one gate; reason: an unread copy would have no segment, against the stated cost $7$ per wire
--   - reading: "Throughout this process, the original register retains both its value and its seven-dimensional label" → between the branch point and the last gate reading the copy, the register is never a target and every gate on its main wire carries the branch label; reason: "this process" is the life of the copy; value and label are kept exactly then
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 5.1, pp.11–12 (PDF 12–13)

import Mathlib
import Definitions.Def_CodedSorting_LocalCircuit

namespace CodedSorting

/-- **Lemma 5.1 (Properties of the local circuit)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), pp.11–12.

Let `v = 111`, `R = 439` and `E = ℚ⁸` with the standard inner product. There exist one-dimensional
rational subspaces `ℓ_t` (`t ∈ [v]`), a permutation `π` of `[v]`, and a binary linear circuit on `v`
pairs of data registers `x, y` and `R` auxiliary registers `z` (661 registers) with nine
temporary wires, implementing `(x, y, z) ↦ (x, y + x, z)`, with subspace labels that grow by
inclusion along each main wire, the input/output labels `x_t : ℓ_t → E`, `y_t : 0 → ℓ_t^⊥`,
`z_r : 0 → E`, temporary wires branching from seven-dimensional register nodes into zero-labeled
gates while the original register keeps its value and label, temporary-wire cost `c = 9 × 7 = 63`,
and `ℓ_t ⊥ ℓ_{π(t)}` for every `t`.

**Formalization Note.** Every clause is a conjunct of `IsLocalCircuit`. The circuit itself is not
printed in the paper (it is the circuit of [eum26, Dre26], checked by computation in the authors'
Lean code). -/
theorem lemma_5_1 :
    ∃ (ℓ : Fin 111 → Submodule ℚ (Fin 8 → ℚ)) (π : Equiv.Perm (Fin 111))
      (C : XorCircuit LocalReg (Fin 9)) (lab : Node LocalReg C.G → Submodule ℚ (Fin 8 → ℚ)),
      IsLocalCircuit ℓ π C lab := by sorry

end CodedSorting
