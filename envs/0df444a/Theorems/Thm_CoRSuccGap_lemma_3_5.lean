-- Prove2me | Theorems.Thm_CoRSuccGap_lemma_3_5
-- name    : CoRSuccGap.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:16.760732+00:00
-- url     : https://prove2.me/theorems/705f9cdc-c37e-43c7-af5b-a41fdaf0b279
-- title:
--   Lemma 3.5 — a composition notices the fold of $\lambda$ only if $S_X$, $S_Y$ or $S_X\cap S_Y$ is $\{\lambda\}$; hence at most two folds
-- statement:
--   Let $\chi$ be a colouring of the pairs of distinct vertices of $V$ with palette $\Lambda=2^{[k]}$ and the two-witness property, and let $\hbar$ be the hub. Let $X,Y$ be colour-determined relations with off-diagonal supports $S_X,S_Y$. Then:
--
--   1. the composition $X;Y$ notices the fold of a colour $\lambda$ only if
--   $$
--   S_X=\{\lambda\},\qquad S_Y=\{\lambda\},\qquad\text{or}\qquad S_X\cap S_Y=\{\lambda\};
--   $$
--   2. hence $X;Y$ notices at most two folds;
--   3. it notices at most one fold if $S_X$ or $S_Y$ is $\emptyset$ or $\Lambda$;
--   4. it notices none if both $S_X$ and $S_Y$ are $\emptyset$ or $\Lambda$.
--
--   Together with Lemma 3.4, this is the counting step of the lower bound: every composition gate can account for at most two folds.
--
--   **Formalization Note** The number of noticed folds is `Set.ncard` of the set of colours $\lambda$ whose fold is noticed; $\Lambda$ as a set of colours is `Set.univ`.
--
--   Differences from the source:
--   - generalization: the standing setting of §3.1: a vertex set of size n ≥ n₀(N) carrying a coloring as in Lemma 3.1, palette of N ≥ 2 colors, palette 2^[k] with k ≥ 1 → any vertex type V and any colouring χ with the two-witness property; reason: the paper fixes such a coloring and its proofs use only the two-witness property; every coloring given by Lemma 3.1 satisfies the hypothesis, so the Lean statement specializes to the source's
--   - generalization: palette 2^[k] for some k ≥ 1 → palette Finset (Fin k) for every k ∈ ℕ; reason: for k = 0 the fold is the identity and no fold is noticed; for k ≥ 1 it is the source's
--   - encoding: "notices at most two (one) folds" → the set of colours whose fold is noticed has ncard ≤ 2 (≤ 1); reason: the palette is finite, so ncard is its cardinality
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Lemma 3.5, p.21 (PDF 23)

import Mathlib
import Definitions.Def_CoRSuccGap_TwoWitness
import Definitions.Def_CoRSuccGap_ColorDet
import Definitions.Def_CoRSuccGap_predict

set_option autoImplicit false

namespace CoRSuccGap

/-- **Lemma 3.5 (When a composition notices a fold).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Lemma 3.5, p.21
(PDF 23): "Let X, Y be color-determined. The composition X; Y notices the fold of λ only if
S_X = {λ}, S_Y = {λ}, or S_X ∩ S_Y = {λ}. Hence it notices at most two folds, at most one if S_X
or S_Y is ∅ or Λ, and none if both are." Standing assumptions: two-witness χ, hub `h`, palette
Λ = 2^[k].

**Formalization Note.** Λ is `Finset (Fin k)` (so "Λ" as a set of colours is `Set.univ`), S_X is
`supp χ X`, the colour λ is `lam`, and "at most two folds" counts the set of noticed colours with
`Set.ncard` (the palette is finite). The standing `k ≥ 1` is not assumed. -/
theorem lemma_3_5 {V : Type*} [DecidableEq V] {k : ℕ} (χ : Sym2 V → Finset (Fin k))
    (hχ : TwoWitness χ) (h : V) (X Y : V → V → Prop) (hX : ColorDet χ X) (hY : ColorDet χ Y) :
    (∀ lam : Finset (Fin k), NoticesComp χ h lam X Y →
      supp χ X = {lam} ∨ supp χ Y = {lam} ∨ supp χ X ∩ supp χ Y = {lam}) ∧
    {lam : Finset (Fin k) | NoticesComp χ h lam X Y}.ncard ≤ 2 ∧
    ((supp χ X = ∅ ∨ supp χ X = Set.univ ∨ supp χ Y = ∅ ∨ supp χ Y = Set.univ) →
      {lam : Finset (Fin k) | NoticesComp χ h lam X Y}.ncard ≤ 1) ∧
    ((supp χ X = ∅ ∨ supp χ X = Set.univ) → (supp χ Y = ∅ ∨ supp χ Y = Set.univ) →
      ∀ lam : Finset (Fin k), ¬ NoticesComp χ h lam X Y) := by sorry

end CoRSuccGap
