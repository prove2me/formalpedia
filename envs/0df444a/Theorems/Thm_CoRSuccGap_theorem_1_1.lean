-- Prove2me | Theorems.Thm_CoRSuccGap_theorem_1_1
-- name    : CoRSuccGap.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:22.141964+00:00
-- url     : https://prove2.me/theorems/ad7cb78b-43ae-448a-a38e-a8e15eb4aad7
-- title:
--   Theorem 1.1 — every CoR circuit or term equivalent to $G_k$ has at least $2^{k-1}$ compositions
-- statement:
--   Let $k\ge 1$ and let $G_k(x,y)=\exists z\bigwedge_{i=1}^k[(P_i(x,y)\wedge Q_i(x,z))\vee(Q_i(x,y)\wedge P_i(x,z))]$ over the signature $P_1,\dots,P_k,Q_1,\dots,Q_k$.
--
--   1. Every relational circuit $C$ over this signature with $[\![C]\!]^{\mathcal M}=[\![G_k]\!]^{\mathcal M}$ on every finite nonempty structure $\mathcal M$ satisfies
--   $$
--   g_{;}(C)\ \ge\ 2^{k-1}.
--   $$
--   2. Every CoR term $T$ over this signature with $[\![T]\!]^{\mathcal M}=[\![G_k]\!]^{\mathcal M}$ on every finite nonempty structure $\mathcal M$ satisfies
--   $$
--   \#_{;}(T)\ \ge\ 2^{k-1}.
--   $$
--
--   Since $G_k$ has size $O(k)$ and the disjunctive-normal-form translation gives a circuit with $2^k$ composition gates, the theorem shows that the exponential blow-up of Tarski's translation from three-variable logic to the calculus of relations is unavoidable, even for circuits, and that the straightforward translation is optimal up to a factor of two in compositions. Only compositions are counted; union, intersection, complement, converse and the constants are free.
--
--   **Formalization Note** Circuits are straight-line programs with the nine CoR gate labels and arbitrary sharing; $g_{;}$ counts every composition gate. $G_k$ is the semantic query.
--
--   Differences from the source:
--   - generalization: C ≡ G_k and T ≡ G_k: agreement on every nonempty structure, finite or infinite → agreement on every finite nonempty structure (D : Type with Fintype D and Nonempty D); reason: a weaker hypothesis, implied by ≡; the paper states that its proof uses only this (p.17, and "or more generally let C agree with G_k on all finite structures", p.22)
--   - encoding: a relational circuit as a DAG; g;(C) counts distinct composition gates → a straight-line program (Circuit) and the number of its gates labelled by composition; reason: a topological numbering of the DAG; same circuits and same count
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Theorem 1.1, p.2 (PDF 4), restated and proved p.22 (PDF 24); ≡ defined §2.3, p.17 (PDF 19)

import Mathlib
import Definitions.Def_CoRSuccGap_Term
import Definitions.Def_CoRSuccGap_Circuit
import Definitions.Def_CoRSuccGap_Gk

set_option autoImplicit false

namespace CoRSuccGap

/-- **Theorem 1.1 (Exponential lower bounds).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Theorem 1.1, p.2 (PDF 4),
restated and proved p.22 (PDF 24): "For every k ≥ 1, every CoR circuit C such that C ≡ G_k and
every CoR term T such that T ≡ G_k satisfy g;(C) ≥ 2^(k−1) and #;(T) ≥ 2^(k−1)." Here Ψ ≡ Γ means
⟦Ψ⟧^M = ⟦Γ⟧^M on every nonempty σ-structure M (§2.3, p.17), and the proof applies "more generally
[to] C [that] agree[s] with G_k on all finite structures" (p.22).

**Formalization Note.** The hypothesis is agreement with the query ⟦G_k⟧ on every finite nonempty
structure (every `D : Type` with `Fintype D` and `Nonempty D`, every interpretation `M` of the 2k
symbols), which is implied by C ≡ G_k; so the statement is the paper's at least. Circuits are
straight-line programs with the nine CoR gate labels, arbitrary sharing and one output; g; counts
every composition gate. -/
theorem theorem_1_1 (k : ℕ) (hk : 1 ≤ k) :
    (∀ C : Circuit (GSym k),
      (∀ (D : Type) [Fintype D] [Nonempty D] (M : GSym k → D → D → Prop),
        C.eval M = Gk k M) →
      2 ^ (k - 1) ≤ C.numCompGates) ∧
    (∀ T : Term (GSym k),
      (∀ (D : Type) [Fintype D] [Nonempty D] (M : GSym k → D → D → Prop),
        T.eval M = Gk k M) →
      2 ^ (k - 1) ≤ T.numComp) := by sorry

end CoRSuccGap
