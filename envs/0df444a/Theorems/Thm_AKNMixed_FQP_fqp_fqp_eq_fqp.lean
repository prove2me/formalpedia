-- Prove2me | Theorems.Thm_AKNMixed_FQP_fqp_fqp_eq_fqp
-- name    : AKNMixed.FQP.fqp_fqp_eq_fqp
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:23:20.494291+00:00
-- url     : https://prove2.me/theorems/984b0aed-2464-4c68-89f9-010e1ff7a7e5
-- title:
--   Theorem 2 — $FQP^{FQP}=FQP$: subroutine calls simulated exactly with $n+l(O(k)+O(r)+O(m))$ gates (corrected: Toffoli added to the gate set; Lemma-4 dilations on a+b+max(a,b) qubits)
-- statement:
--   For every bound $d$ on the order of gates there is a constant $c$ with the following property. Let $\mathcal G$ be a set of quantum gates of order at most $(d,d)$, and for each $g\in\mathcal G$ let $U_g$ be any Lemma-4 unitary dilation of $g$. Let $\mathcal S$ be a set of probabilistic functions from $m$ to $r$ bits, each computed exactly by some well-formed circuit over $\mathcal G$ with at most $k$ gates. Let $Q$ be a well-formed circuit over $\mathcal G$ and $\mathcal S$ with $n$ nodes labeled by gates and $l$ nodes labeled by subroutines. Then there is a well-formed circuit $\tilde Q$ with no subroutines, the same inputs and results as $Q$, all of whose gates lie in
--
--   $$\mathcal U_{\mathcal G}\cup\mathcal U_{\mathcal G}^{\dagger}\cup\{C,\ \text{Toffoli}\},$$
--
--   with at most
--
--   $$n+l\,(ck+cr+cm)$$
--
--   gates, and with $f_{\tilde Q}=f_Q$ exactly.
--
--   In the language of complexity classes ($FQP$ = probabilistic functions computed by uniform polynomial-size quantum circuits) this gives $FQP^{FQP}=FQP$: quantum circuits may call probabilistic subroutines, on superpositions of inputs, at polynomial cost.
--
--   Differences from the source:
--   - correction: gates from U_G ∪ U_G† ∪ C → gates from dilationGateSet G u = U_G ∪ U_G† ∪ {C, Toffoli}; reason: the printed theorem is false: for G = {Hadamard} with the valid dilation U_H = H ⊗ I ⊗ I every circuit over {H ⊗ I ⊗ I, CNOT} is a stabilizer circuit, whose output distributions (and their marginals) are uniform on affine subspaces; but the circuit Q = H on input a, g_s on (a; blank c) with s a uniform random bit (k = 1), then H on c and on a, results (c, a), has f_Q(0) = (1/2, 0, 1/4, 1/4); the proof's garbage flag and conditioned input copy need Toffoli
--   - reading: n + l(O(k) + O(r) + O(m)) → ∀ d ∃ c, for gates of order ≤ (d, d): size ≤ n + l(c k + c r + c m), c independent of G, u, S, m, r, k, Q; reason: the paper's gates are local (p. 2: "involves only a constant number of qubits"); a dilation of an order-(a, b) gate has a + b + max(a, b) ≤ 3d wires of potential garbage, so the constant may depend on the order bound
--   - reading: U_G the unitary gates corresponding to gates from G, according to lemma 4 → every family u with IsLemma4Dilation g (u g hg) for all g ∈ G; reason: the stronger of the two readings: the conclusion holds whichever Lemma-4 dilations are chosen
--   - correction: U_G according to lemma 4, i.e. dilations on 2a + b qubits with a + b blanks for a gate of order (a, b) → IsLemma4Dilation on a + b + max(a, b) qubits with b + max(a, b) blanks (the printed size when b ≤ a); reason: Lemma 4 as printed is false for b > a (ρ ↦ Tr(ρ)·I/4 of order (1, 2) has Choi rank 8 > 4, the most a 4-qubit unitary with 2 qubits traced out can produce), so with the printed size the hypothesis on u would be unsatisfiable for such G and the theorem would say nothing about them
--   - generalization: U_d defined by U_d|i, 0⟩ = |i, d(i)⟩ → subroutine nodes act with U_d|i, x⟩ = |i, x ⊕ d(i)⟩ for every x; reason: agrees with the paper on |i, 0⟩, where the paper defines it; Q may also feed non-blank wires into a subroutine's output register, so Q ranges over more circuits
--   - encoding: a directed acyclic graph with blank inputs and result outputs; n gates and l subroutines; computable by circuits using no more than k gates → Circuit over a wire pool with WellFormed (hypothesis on Q and on each Q_s, conclusion on Q̃); n = Q.gateCount, l = Q.subCount; Q_s : Circuit G ∅ m r with Qs.size ≤ k and Qs.computedFun = s.prob; Q̃ over the gate set with subroutine set ∅ and Q̃.size counting all its nodes; reason: wire-pool encoding of Definition 2; any DAG with any topological sort is such a list
--   - encoding: G a set of gates → G : Set QGate with every g ∈ G satisfying IsQuantum; reason: gates are unbundled: Definition 1's properties are a hypothesis
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Theorem 2, p. 11 (class form p. 3)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_ProbFun
import Definitions.Def_AKNMixed_FQP_Circuit
import Definitions.Def_AKNMixed_FQP_Circuit_computedFun
import Definitions.Def_AKNMixed_FQP_IsLemma4Dilation
import Definitions.Def_AKNMixed_FQP_dilationGateSet

namespace AKNMixed.FQP

open QAlgorithms

/-- **Theorem 2 (FQP^FQP = FQP), with Toffoli added to the gate set: a circuit calling
probabilistic subroutines is computed exactly by a circuit over `U_G ∪ U_G† ∪ {C, Toffoli}` with
`n + l(O(k) + O(r) + O(m))` gates.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Theorem 2, p. 11 (class form p. 3): "Let G be a set of gates, S a set of probabilistic functions
from m to r bits, computable by quantum circuits using no more than k gates from G. Let Q be a
quantum circuit, which uses n gates from G, and l subroutines from S, there exists a quantum
circuit Q̃ which uses no more then n + l(O(k) + O(r) + O(m)) gates from U_G ∪ U_G† ∪ C and
computes f_Q."

For every bound `d` on gate orders there is a constant `c` such that: for every set `G` of
quantum gates of order at most `(d, d)`, every choice `u` of Lemma-4 dilations of the gates of
`G`, every `m, r, k`, every set `S` of probabilistic functions from `m` to `r` bits each computed
by a well-formed circuit over `G` with at most `k` gates, and every well-formed circuit `Q` over
`G` and `S` with `n` gate nodes and `l` subroutine nodes, there is a well-formed circuit `Q̃`
over `U_G ∪ U_G† ∪ {C, Toffoli}`, with no subroutines and the same inputs and results, with at
most `n + l(ck + cr + cm)` nodes, and `f_Q̃ = f_Q` exactly.

**Formalization Note.** (1) Correction: the printed gate set `U_G ∪ U_G† ∪ C` is too small
(G = {Hadamard} with the dilation `H ⊗ I ⊗ I` gives only stabilizer circuits, which cannot
produce the distribution `(1/2, 0, 1/4, 1/4)` of a 3-gate circuit with one uniform-bit
subroutine); Toffoli is added. (2) `O(·)` is read as `∀ d ∃ c`, the constant depending only on
the locality bound `d` of the gates. (3) The statement holds for every family `u` of Lemma-4
dilations; Lemma 4's register is `a + b + max a b` qubits for a gate of order `(a, b)` (the
printed `2a + b` when `b ≤ a`; see `IsLemma4Dilation` for why `2a + b` is too small when
`b > a`). (4) Subroutines act by `g_f` with the exclusive-or completion of `U_d`. -/
theorem fqp_fqp_eq_fqp :
    ∀ d : ℕ, ∃ c : ℕ, ∀ (G : Set QGate), (∀ g ∈ G, g.IsQuantum) →
      (∀ g ∈ G, g.inOrd ≤ d ∧ g.outOrd ≤ d) →
      ∀ (u : ∀ g ∈ G,
          Matrix (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd))
            (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd)) ℂ),
        (∀ (g : QGate) (hg : g ∈ G), IsLemma4Dilation g (u g hg)) →
      ∀ (m r k : ℕ) (S : Set (ProbFun m r)),
        (∀ s ∈ S, ∃ Qs : Circuit G (∅ : Set (ProbFun m r)) m r,
            Qs.WellFormed ∧ Qs.size ≤ k ∧ Qs.computedFun = s.prob) →
      ∀ (nIn rOut : ℕ) (Q : Circuit G S nIn rOut), Q.WellFormed →
        ∃ Qt : Circuit (dilationGateSet G u) (∅ : Set (ProbFun m r)) nIn rOut,
          Qt.WellFormed ∧
          Qt.size ≤ Q.gateCount + Q.subCount * (c * k + c * r + c * m) ∧
          Qt.computedFun = Q.computedFun := by sorry

end AKNMixed.FQP
