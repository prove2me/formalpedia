-- Prove2me | Theorems.Thm_CodedSorting_corollary_5_4
-- name    : CodedSorting.corollary_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:26.081334+00:00
-- url     : https://prove2.me/theorems/a3f3d349-24f4-482a-ba5e-798c13d80910
-- title:
--   Corollary 5.4 — a permuting labeled circuit with $W$ inputs, total length $S$, and $S/W<512^{\tau}$
-- statement:
--   Take $m=512$, $W=24{,}432{,}543$, $S=12{,}508{,}242{,}237$, $\varepsilon=3/200000$ and $\tau=1-\varepsilon$. There is a binary linear circuit on $W$ input registers that permutes the input bits (input $i$ is recovered at output $\sigma(i)$ for a permutation $\sigma$), with admissible subspace labels in $\mathbb Q^{512}$ of total edge length $S$ and the session label conditions of Lemma 5.3 ($U_{t_{\sigma(i)}}=U_{s_i}^\perp$, full dimension and full rank), and
--   $$\eta=1-\frac{S}{Wm}=\frac{33}{338432},\qquad \frac{S}{W}<m^{\tau}.\tag{13}$$
--
--   The inequality $S/W<m^\tau$ is the exponent saving of the address-field interchange recursion (Lemma 6.1): one interchange reduces to $S$ child interchanges on $1/W$ of the data.
--
--   Differences from the source:
--   - reading: "The circuit permutes the input bits and has the matrix-label properties proved above" → there exist a permutation $\sigma$ of `Fin W`, a circuit implementing $x\mapsto x\circ\sigma^{-1}$ and labels with `LabeledCircuit`, `SessionLabels` and total length $S$; reason: "the circuit" is the circuit of Lemmas 5.2–5.3; these are the properties §6 uses
--   - generalization: the session conditions (9) → also $U_{t_{\sigma(i)}}=U_{s_i}^\perp$; reason: proved for this circuit in Lemma 5.3 and used in Lemma 6.2; dropping it gives the printed claim
--   - encoding: $\eta$ → $1-S/(Wm)$; reason: definition (10), p.17
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Corollary 5.4, p.18 (PDF 19), with (10), p.17 (PDF 18)

import Mathlib
import Definitions.Def_CodedSorting_Sessions
import Definitions.Def_CodedSorting_Exponent

namespace CodedSorting

/-- **Corollary 5.4 (Fixed parameters for the recursion)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.18.

Take `m = 512`, `W = 24,432,543`, `S = 12,508,242,237`, `ε = 1.5 × 10⁻⁵`, `τ = 1 − ε`. There is a
binary linear circuit on `W` input registers that permutes the input bits (input `i` is recovered at
output `σ(i)`), with subspace labels in `ℚ⁵¹²` nested along every edge, total edge length `S`, and
the source/sink label properties of Lemma 5.3; and `η = 1 − S/(Wm) = 33/338432`, `S/W < m^τ`.

**Formalization Note.** The `W` registers are indexed by `Fin W`. "The matrix-label properties
proved above" are `LabeledCircuit` (nested labels, (6)–(7)) and `SessionLabels` ((9) with
`U_t = U_s^⊥`), with `totalLength = S` ((8)). `η` is defined by (10), p.17. `ε = 3/200000`. -/
theorem corollary_5_4 :
    ∃ (σ : Equiv.Perm (Fin 24432543)) (n : ℕ) (C : XorCircuit (Fin 24432543) (Fin n))
      (lab : Node (Fin 24432543) C.G → Submodule ℚ (Fin 512 → ℚ)),
      C.Implements (fun x i => x (σ.symm i)) ∧
      LabeledCircuit C lab ∧
      totalLength C lab = 12508242237 ∧
      SessionLabels C σ lab ∧
      (1 : ℝ) - 12508242237 / (24432543 * 512) = 33 / 338432 ∧
      (12508242237 : ℝ) / 24432543 < (512 : ℝ) ^ tau := by sorry

end CodedSorting
