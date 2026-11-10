-- Prove2me | Theorems.Thm_CoRSuccGap_lemma_3_1
-- name    : CoRSuccGap.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:18.895365+00:00
-- url     : https://prove2.me/theorems/2b621bdf-7d5b-4288-9bc5-7237c20b836b
-- title:
--   Lemma 3.1 — two-witness colourings exist on $n\ge\lceil 12N^2\ln(2N)\rceil+3$ vertices
-- statement:
--   Let $\Lambda$ be a palette of $N\ge 2$ colours and let $V$ be a finite vertex set with
--
--   $$
--   |V|\;\ge\; n_0(N):=\big\lceil 12N^2\ln(2N)\big\rceil+3 .
--   $$
--
--   Then there is a colouring $\chi$ of the pairs of distinct vertices of $V$ with $\Lambda$ such that for all distinct $u,v\in V$ and all colours $\mu,\nu\in\Lambda$ at least two distinct vertices $z\in V\setminus\{u,v\}$ satisfy $\chi(u,z)=\mu$ and $\chi(z,v)=\nu$.
--
--   The lemma supplies the vertex sets on which the reference structures of Section 3 live: one witness makes colour-determined relations closed under the CoR operations, the second survives the removal of the hub.
--
--   **Formalization Note** $N$ is `Fintype.card Λ`, $\ln$ is `Real.log` and the ceiling is `Nat.ceil`; the threshold is the exact $n_0(N)$ of the paper.
--
--   Differences from the source:
--   - encoding: a vertex set V of size n ≥ n₀(N) and a coloring of the pairs of distinct vertices → a finite type V with Fintype.card V ≥ n₀(N) and χ : Sym2 V → Λ whose diagonal values are unused; reason: Lean representation; the same colourings
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Lemma 3.1, p.18 (PDF 20)

import Mathlib
import Definitions.Def_CoRSuccGap_TwoWitness

set_option autoImplicit false

namespace CoRSuccGap

/-- **Lemma 3.1 (Two witnesses).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Lemma 3.1, p.18 (PDF 20): "For every integer
n ≥ n₀(N) := ⌈12N² ln(2N)⌉ + 3, there is a coloring such that, for all distinct u, v ∈ V and all
μ, ν ∈ Λ, at least two distinct vertices z ∈ V \ {u, v} satisfy χ(u, z) = μ and χ(z, v) = ν."
The palette Λ has N ≥ 2 colours (§3.1, p.17).

**Formalization Note.** N is `Fintype.card Λ`, n is `Fintype.card V`, ln is `Real.log`, and the
ceiling is `Nat.ceil` (its argument is positive). A colouring is `χ : Sym2 V → Λ`; its diagonal
values play no role in `TwoWitness`. -/
theorem lemma_3_1 (Λ : Type*) [Fintype Λ] (hN : 2 ≤ Fintype.card Λ) (V : Type*) [Fintype V]
    (hn : Nat.ceil (12 * (Fintype.card Λ : ℝ) ^ 2 * Real.log (2 * (Fintype.card Λ : ℝ))) + 3 ≤
      Fintype.card V) :
    ∃ χ : Sym2 V → Λ, TwoWitness χ := by sorry

end CoRSuccGap
