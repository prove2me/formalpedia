-- Prove2me | Theorems.Thm_AKNMixed_FQP_final_eq_of_perm
-- name    : AKNMixed.FQP.final_eq_of_perm
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:21:41.461491+00:00
-- url     : https://prove2.me/theorems/eb957dc3-447a-4fa8-8eda-205bc22f1209
-- title:
--   Lemma 2 — the final density matrix does not depend on the topological sort
-- statement:
--   Let every gate of $\mathcal G$ be a quantum gate and let $Q$ be a well-formed circuit over $\mathcal G$ (and possibly subroutines). If the nodes $g_1,\dots,g_t$ of $Q$ are listed in another order $g_{\sigma(1)},\dots,g_{\sigma(t)}$ that is again a topological sort of the same circuit, then for every initial matrix $\rho$
--
--   $$g_t\circ\cdots\circ g_2\circ g_1\circ\rho=g_{\sigma(t)}\circ\cdots\circ g_{\sigma(2)}\circ g_{\sigma(1)}\circ\rho .$$
--
--   So the final density matrix $Q\circ\rho$ of Definition 3 is well defined.
--
--   Differences from the source:
--   - encoding: two topological sorts of the same quantum circuit → a permutation l' of the node list such that the circuit with nodes l' is again WellFormed; reason: in the wire-pool encoding the edges are the shared wire labels, so a well-formed reordering is exactly another topological sort
--   - generalization: a circuit of gates from G (§3) → a circuit over G and any set S of subroutines (subroutine nodes act by g_f); reason: taking S = ∅ gives the paper's statement; the paper uses Definition 3 also for circuits with subroutines (Theorem 2)
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 2, p. 8

import Mathlib
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_ProbFun
import Definitions.Def_AKNMixed_FQP_Circuit
import Definitions.Def_AKNMixed_FQP_Circuit_final

namespace AKNMixed.FQP

open QAlgorithms

/-- **Lemma 2: the final density matrix does not depend on the topological sort.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 2, p. 8: "g_t ∘ ... ∘ g_2 ∘ g_1 ∘ ρ = g_σ(t) ∘ ... ∘ g_σ(2) ∘ g_σ(1) ∘ ρ, where σ is a
permutation, If the two orderings are two topological sorts of the same quantum circuit."

Let every gate of `G` be a quantum gate, and let `Q` be a well-formed circuit over `G` and the
subroutines `S`. If `l'` is a permutation of the node list of `Q` such that the circuit `Q'`
obtained by listing the nodes in the order `l'` is again well formed, then `Q'.final = Q.final`
(as maps on all matrices of the wire pool).

**Formalization Note.** A circuit lists its nodes in a topological order over a pool of wire
labels; a permutation of the list that is again well formed is exactly another topological sort
of the same graph (the edges are the shared wire labels). Gates are assumed to be quantum gates,
as in the paper; subroutine nodes act by `g_f`. -/
theorem final_eq_of_perm {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)} {nIn r : ℕ}
    (hG : ∀ g ∈ G, g.IsQuantum) (Q : Circuit G S nIn r) (l' : List (Node G S Q.N))
    (hperm : Q.nodes.Perm l') (hQ : Q.WellFormed)
    (hQ' : ({ Q with nodes := l' } : Circuit G S nIn r).WellFormed) :
    ({ Q with nodes := l' } : Circuit G S nIn r).final = Q.final := by sorry

end AKNMixed.FQP
