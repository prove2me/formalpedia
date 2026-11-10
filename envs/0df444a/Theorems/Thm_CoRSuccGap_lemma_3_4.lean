-- Prove2me | Theorems.Thm_CoRSuccGap_lemma_3_4
-- name    : CoRSuccGap.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:17.692462+00:00
-- url     : https://prove2.me/theorems/57b5fc4c-4b3c-4791-b00f-933159c8dfdf
-- title:
--   Lemma 3.4 — if no composition gate notices the fold of $\lambda$, every gate computes its prediction on $\mathcal M_\lambda$
-- statement:
--   Let $\chi$ be a colouring of the pairs of distinct vertices of $V$ with palette $2^{[k]}$ and the two-witness property, $\hbar$ the hub and $\lambda$ a colour. Let $\mathcal M_0$ be a **reference structure** on $V$ (every input relation is colour-determined) and let $\mathcal M_\lambda$ be the **folded structure**, which replaces every input relation by its prediction. Let $C$ be a relational circuit. A composition gate of $C$ notices the fold of $\lambda$ if the composition of its two operand values on $\mathcal M_0$ notices it. If no composition gate of $C$ notices the fold of $\lambda$, then
--
--   1. on $\mathcal M_\lambda$ every gate $g$ of $C$ computes the prediction of its value on $\mathcal M_0$: $[\![g]\!]^{\mathcal M_\lambda}=\big([\![g]\!]^{\mathcal M_0}\big)^{(\lambda)}$;
--   2. in particular, $[\![C]\!]^{\mathcal M_0}(u,v)=[\![C]\!]^{\mathcal M_\lambda}(u,v)$ at every pair $(u,v)$ that the fold does not recolour.
--
--   This reduces the circuit lower bound to the local question of how many folds a single composition can notice.
--
--   **Formalization Note** The operands of composition gate $i$ are its two earlier gates. "The fold does not recolour $(u,v)$" is `lab (fold χ h lam) u v = lab χ u v`.
--
--   Differences from the source:
--   - generalization: the standing setting of §3.1: a vertex set of size n ≥ n₀(N) carrying a coloring as in Lemma 3.1, palette of N ≥ 2 colors, palette 2^[k] with k ≥ 1 → any vertex type V and any colouring χ with the two-witness property; reason: the paper fixes such a coloring and its proofs use only the two-witness property; every coloring given by Lemma 3.1 satisfies the hypothesis, so the Lean statement specializes to the source's
--   - generalization: palette 2^[k] for some k ≥ 1; a finite signature → palette Finset (Fin k) for every k ∈ ℕ; any signature type σ; reason: neither is used; the source's case is an instance
--   - encoding: a relational circuit as a DAG → a straight-line program whose gate i reads earlier gates (Circuit); reason: a topological numbering of the DAG; same circuits
--   - encoding: a pair (u, v) that the fold of λ does not recolor → lab (fold χ h lam) u v = lab χ u v; reason: for k ≥ 1, λᶜ ≠ λ, so the label of a pair changes exactly when the fold recolors it
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Lemma 3.4, p.20 (PDF 22); noticing for gates and M_λ, p.20 (PDF 22)

import Mathlib
import Definitions.Def_CoRSuccGap_Circuit
import Definitions.Def_CoRSuccGap_TwoWitness
import Definitions.Def_CoRSuccGap_ColorDet
import Definitions.Def_CoRSuccGap_predict

set_option autoImplicit false

namespace CoRSuccGap

/-- **Lemma 3.4 (Unnoticed folds).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Lemma 3.4, p.20 (PDF 22): "Let C be a
relational circuit and λ a color. If no composition gate of C notices the fold of λ, then on M_λ
every gate of C computes the prediction of its value on M₀. In particular, the outputs of C on M₀
and on M_λ agree at every pair that the fold does not recolor." A composition gate notices the fold
if the composition of its operand values on M₀ notices it (p.20); M₀ is a reference structure
(every input relation colour-determined, p.19) and M_λ replaces every input relation by its
prediction (p.20). Standing assumptions: two-witness χ, hub `h`, palette 2^[k].

**Formalization Note.** Circuits are straight-line programs (`Circuit`); the operands `a, b` of
gate `i` are earlier gates, cast to indices of the circuit. "The fold does not recolor (u, v)" is
`lab (fold χ h lam) u v = lab χ u v`. The signature σ is any type; the standing `k ≥ 1` is not
assumed. -/
theorem lemma_3_4 {σ : Type*} {V : Type*} [DecidableEq V] {k : ℕ}
    (χ : Sym2 V → Finset (Fin k)) (hχ : TwoWitness χ) (h : V) (lam : Finset (Fin k))
    (C : Circuit σ) (M₀ : σ → V → V → Prop) (hM₀ : ∀ r, ColorDet χ (M₀ r))
    (hno : ∀ (i : Fin C.size) (a b : Fin i), C.gate i = Gate.comp a b →
      ¬ NoticesComp χ h lam (C.gateVal M₀ ⟨a.val, a.isLt.trans i.isLt⟩)
          (C.gateVal M₀ ⟨b.val, b.isLt.trans i.isLt⟩)) :
    (∀ i : Fin C.size,
        C.gateVal (fun r => predict χ h lam (M₀ r)) i = predict χ h lam (C.gateVal M₀ i)) ∧
    (∀ u v : V, lab (fold χ h lam) u v = lab χ u v →
        (C.eval (fun r => predict χ h lam (M₀ r)) u v ↔ C.eval M₀ u v)) := by sorry

end CoRSuccGap
