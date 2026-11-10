-- Prove2me | Theorems.Thm_CoRSuccGap_lemma_3_6
-- name    : CoRSuccGap.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:32.925018+00:00
-- url     : https://prove2.me/theorems/c00ffa0d-283d-4754-9d7f-5499ded74931
-- title:
--   Lemma 3.6 — the tests for $G_k$: $G_k(\hbar,v_{\lambda^c})$ holds in $\mathcal M_0$ and fails in $\mathcal M_\lambda$; $G_k^{\forall}$ is true in $\mathcal M_0$, false in every $\mathcal M_\lambda$
-- statement:
--   Let $k\ge 1$, let $\chi$ be a colouring of the pairs of distinct vertices of $V$ with palette $2^{[k]}$ and the two-witness property, let $\hbar$ be the hub, let $\mathcal M_0$ be the reference structure for $G_k$ (on an edge of colour $\mu$, $P_i$ holds iff $i\in\mu$ and $Q_i$ iff $i\notin\mu$; both fail on loops), and let $\mathcal M_\lambda$ be its fold. Then:
--
--   1. for every colour $\lambda$ and every vertex $v\neq\hbar$ with $\chi(\hbar,v)=\lambda^c$,
--   $$
--   [\![G_k]\!]^{\mathcal M_0}(\hbar,v)=1,\qquad [\![G_k]\!]^{\mathcal M_\lambda}(\hbar,v)=0;
--   $$
--   2. the sentence $G_k^{\forall}=\forall x\,\forall y\,(x=y\vee G_k(x,y))$ is true in $\mathcal M_0$ and, when $V$ has at least two vertices, false in every $\mathcal M_\lambda$.
--
--   Thus $G_k$ and $G_k^{\forall}$ each supply $2^k$ tests: for each colour $\lambda$, a pair whose answer changes under the fold of $\lambda$ although the fold does not recolour it.
--
--   **Formalization Note** The paper fixes one vertex $v_{\lambda^c}$ with $\chi(\hbar,v_{\lambda^c})=\lambda^c$; the first clause holds for every such vertex. The vertex set may be infinite.
--
--   Differences from the source:
--   - generalization: the standing setting of §3.1: a vertex set of size n ≥ n₀(N) carrying a coloring as in Lemma 3.1, palette of N ≥ 2 colors, palette 2^[k] → any vertex type V and any colouring χ with the two-witness property; reason: the paper fixes such a coloring and its proofs use only the two-witness property; every coloring given by Lemma 3.1 satisfies the hypothesis, so the Lean statement specializes to the source's
--   - generalization: the fixed vertex v_{λᶜ} with χ(ℏ, v_{λᶜ}) = λᶜ → every vertex v ≠ ℏ with χ(ℏ, v) = λᶜ; reason: v_{λᶜ} is one such vertex
--   - encoding: the standing size n ≥ n₀(2^k) of V (proof of Theorem 1.1) → Nontrivial V, assumed only for "G_k^∀ is false in every M_λ"; reason: n₀(2^k) ≥ 70, so the paper's V is nontrivial; on a one-vertex set G_k^∀ holds in every structure
--   - encoding: v_{λᶜ} as a vertex of the colouring χ : (V choose 2) → Λ → v ≠ ℏ explicitly; reason: χ is defined on pairs of distinct vertices only
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Lemma 3.6, p.22 (PDF 24); M₀ p.22 (PDF 24); v_μ p.18 (PDF 20)

import Mathlib
import Definitions.Def_CoRSuccGap_Gk
import Definitions.Def_CoRSuccGap_TwoWitness
import Definitions.Def_CoRSuccGap_ColorDet
import Definitions.Def_CoRSuccGap_predict
import Definitions.Def_CoRSuccGap_refGk

set_option autoImplicit false

namespace CoRSuccGap

/-- **Lemma 3.6 (The tests for G_k).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Lemma 3.6, p.22 (PDF 24): "For every
color λ, ⟦G_k⟧^{M₀}(ℏ, v_{λᶜ}) = 1, ⟦G_k⟧^{M_λ}(ℏ, v_{λᶜ}) = 0. Moreover, the sentence
G_k^∀ = ∀x ∀y (x = y ∨ G_k(x, y)) of §1.1 is true in M₀ and false in every M_λ." Here M₀ is the
reference structure of §3.5 (`refGk χ`), M_λ its fold (every input relation replaced by its
prediction, p.20), and v_μ a vertex with χ(ℏ, v_μ) = μ (§3.1, p.18). Standing assumptions:
two-witness χ, hub `h` = ℏ, palette 2^[k] with k ≥ 1.

**Formalization Note.** The first clause is stated for every vertex `v ≠ h` with
`χ s(h, v) = lamᶜ`, not only for the one fixed v_{λᶜ}. The claim that G_k^∀ is false in every
M_λ assumes `Nontrivial V`: on a one-vertex set G_k^∀ holds in every structure, while the paper's V
has n ≥ n₀(2^k) ≥ 2 vertices. The vertex set may be infinite. -/
theorem lemma_3_6 {V : Type*} [DecidableEq V] {k : ℕ} (hk : 1 ≤ k)
    (χ : Sym2 V → Finset (Fin k)) (hχ : TwoWitness χ) (h : V) :
    (∀ (lam : Finset (Fin k)) (v : V), v ≠ h → χ s(h, v) = lamᶜ →
      Gk k (refGk χ) h v ∧ ¬ Gk k (fun r => predict χ h lam (refGk χ r)) h v) ∧
    GkForall k (refGk χ) ∧
    (Nontrivial V → ∀ lam : Finset (Fin k),
      ¬ GkForall k (fun r => predict χ h lam (refGk χ r))) := by sorry

end CoRSuccGap
