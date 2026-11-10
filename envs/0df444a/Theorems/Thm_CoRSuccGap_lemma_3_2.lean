-- Prove2me | Theorems.Thm_CoRSuccGap_lemma_3_2
-- name    : CoRSuccGap.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:39.924777+00:00
-- url     : https://prove2.me/theorems/465cc5be-fb3a-475c-89c6-848b38b51bca
-- title:
--   Lemma 3.2 — colour-determined relations are closed under the CoR operations, with colour table (CT) for composition
-- statement:
--   Let $\chi$ be a colouring of the pairs of distinct vertices of $V$ with the two-witness property of Lemma 3.1. Then:
--
--   1. the constants $\mathbf 0,\mathbf 1,\mathbf{id}$ are colour-determined;
--   2. colour-determined relations are closed under union, intersection, complement, converse and composition;
--   3. for colour-determined $X,Y$ the composition has the colour table (CT): for every colour $\mu\in\Lambda$,
--
--   $$
--   (X;Y)[\mu]=\big(X[\mathbf{id}]\wedge Y[\mu]\big)\vee\big(X[\mu]\wedge Y[\mathbf{id}]\big)\vee\big(S_X\neq\emptyset\wedge S_Y\neq\emptyset\big),
--   $$
--   $$
--   (X;Y)[\mathbf{id}]=\big(X[\mathbf{id}]\wedge Y[\mathbf{id}]\big)\vee\big(S_X\cap S_Y\neq\emptyset\big).
--   $$
--
--   In particular every value a relational circuit computes on a reference structure is colour-determined, and its table is computed entrywise from those of its operands.
--
--   **Formalization Note** (CT) is stated pointwise: at every pair $u\neq v$ with $\chi(u,v)=\mu$, $(X;Y)(u,v)$ holds iff the first right-hand side holds, and at every loop $(u,u)$ iff the second does.
--
--   Differences from the source:
--   - generalization: the standing setting of §3.1: a vertex set of size n ≥ n₀(N) carrying a coloring as in Lemma 3.1, palette of N ≥ 2 colors → any vertex type V and any colouring χ with the two-witness property; reason: the paper fixes such a coloring and its proofs use only the two-witness property; every coloring given by Lemma 3.1 satisfies the hypothesis, so the Lean statement specializes to the source's
--   - generalization: palette of N ≥ 2 colors → any palette type Λ; reason: the statement and proof do not use N ≥ 2; it specializes to the source's palettes
--   - encoding: (CT) as an identity of table entries (X;Y)[μ], (X;Y)[id] → pointwise equivalences at every pair u ≠ v of colour μ and at every loop; reason: for colour-determined relations the table entry is the value at every pair with that label, so the two forms say the same
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Lemma 3.2, p.19 (PDF 21)

import Mathlib
import Definitions.Def_CoRSuccGap_TwoWitness
import Definitions.Def_CoRSuccGap_ColorDet

set_option autoImplicit false

namespace CoRSuccGap

/-- **Lemma 3.2 (Closure of color-determined relations).** Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Lemma 3.2,
p.19 (PDF 21): "The constants 0, 1, id are color-determined, and color-determined relations are
closed under Boolean operations, converse, and composition. For color-determined X, Y, their
composition has the following color table (CT), for every color μ ∈ Λ:
(X; Y)[μ] = (X[id] ∧ Y[μ]) ∨ (X[μ] ∧ Y[id]) ∨ (S_X ≠ ∅ ∧ S_Y ≠ ∅),
(X; Y)[id] = (X[id] ∧ Y[id]) ∨ (S_X ∩ S_Y ≠ ∅)." Standing assumption: χ has the two-witness
property of Lemma 3.1 (§3.1, p.18, "Fix such a coloring").

**Formalization Note.** Relations are `V → V → Prop`; 0, 1, id are `False`, `True`, `=`.
Boolean operations are union, intersection and complement. (CT) is stated pointwise: at every pair
`u ≠ v` of colour μ and at every loop `(u, u)`, the composition holds iff the right-hand side of
(CT) does. The two-witness property replaces the standing size n ≥ n₀(N) and the palette is any
type. -/
theorem lemma_3_2 {V : Type*} {Λ : Type*} [DecidableEq V] (χ : Sym2 V → Λ)
    (hχ : TwoWitness χ) :
    (ColorDet χ (fun _ _ => False) ∧ ColorDet χ (fun _ _ => True) ∧
      ColorDet χ (fun a b => a = b)) ∧
    (∀ X Y : V → V → Prop, ColorDet χ X → ColorDet χ Y →
      ColorDet χ (fun a b => X a b ∨ Y a b) ∧ ColorDet χ (fun a b => X a b ∧ Y a b) ∧
      ColorDet χ (fun a b => ¬ X a b) ∧ ColorDet χ (fun a b => X b a) ∧
      ColorDet χ (fun a b => ∃ c, X a c ∧ Y c b)) ∧
    (∀ X Y : V → V → Prop, ColorDet χ X → ColorDet χ Y →
      (∀ (μ : Λ) (u v : V), u ≠ v → χ s(u, v) = μ →
        ((∃ c, X u c ∧ Y c v) ↔
          (tab χ X none ∧ tab χ Y (some μ)) ∨ (tab χ X (some μ) ∧ tab χ Y none) ∨
            ((supp χ X).Nonempty ∧ (supp χ Y).Nonempty))) ∧
      (∀ u : V, ((∃ c, X u c ∧ Y c u) ↔
          (tab χ X none ∧ tab χ Y none) ∨ (supp χ X ∩ supp χ Y).Nonempty))) := by sorry

end CoRSuccGap
