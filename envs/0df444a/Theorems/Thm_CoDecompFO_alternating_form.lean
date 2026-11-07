-- Prove2me | Theorems.Thm_CoDecompFO_alternating_form
-- name    : CoDecompFO.alternating_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:16.053894+00:00
-- url     : https://prove2.me/theorems/754d5528-fb8b-4cef-a89a-8b2401a27cc0
-- title:
--   Proof of Theorem 1.16, first step — a computable alternating form with equality
-- statement:
--   Let $\sigma$ be a finite relational signature. There is a computable map on codes that takes every $\sigma$-sentence $\varphi$, with equality, to a number $\ell\le|\varphi|$ and a matrix $\psi$ on $[2\ell]$ over $\sigma$ together with $\circ$, with $|\psi|\le 2|\varphi|$, such that for every non-empty $\sigma$-structure $M$
--   $$
--   M\models\varphi\quad\Longleftrightarrow\quad M^\circ\models\forall x_1\exists y_1\cdots\forall x_\ell\exists y_\ell\;\psi(\vec x,\vec y).
--   $$
--
--   This is the first step of the algorithm: prenex normal form, a dummy quantifier for each missing alternation, and $\circ$ for equality.
--
--   Differences from the source:
--   - reading: "Put φ into alternating prenex normal form", silent on the empty structure → the equivalence is stated for non-empty structures; reason: on an empty structure, (∀x Rx) ∧ ⊥ is false and its prenex form ∀x (Rx ∧ ⊥) is true; the goal treats an empty limit directly
--   - generalization: FO without equality, with the ∘ relation of A.6 for equality → a Mathlib sentence, equality included, translated to ∘; reason: A.9 asks this of equality; a sentence without equality is the paper's case
--   - generalization: no bounds and no algorithm named for this step → a computable map on codes with ℓ ≤ |φ| and |ψ| ≤ 2|φ|; reason: the algorithm runs this step, and forgetting the bounds gives the printed step
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), proof of Theorem 1.16, p.41; ¶5.5, p.18; A.6–A.9, p.53

import Mathlib
import Definitions.Def_CoDecompFO_AltSat
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Alternating form, with equality** (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…,
proof of Theorem 1.16, p.41, first step: "Put φ into alternating prenex normal form"; ¶5.5, p.18;
A.6–A.9, p.53). There is a computable map on codes taking each `σ`-sentence `φ` with equality to
`ℓ ≤ |φ|` and a matrix `ψ` on `[2ℓ]` over `σ` with `∘`, with `|ψ| ≤ 2|φ|`, such that for every nonempty
`M`, `M ⊨ φ` iff `M° ⊨ ∀x₁∃y₁ ⋯ ∀x_ℓ∃y_ℓ ψ`.

**Formalization Note** `[Nonempty M]` is required: Mathlib's prenexing, and padding with dummy
quantifiers, are only sound on nonempty structures. -/
theorem alternating_form (σ : Sig) :
    ∃ F : List ℕ → List ℕ, Computable F ∧
      ∀ φ : σ.lang.Sentence,
        ∃ (ℓ : ℕ) (ψ : (sigmaEq σ).lang.BoundedFormula Empty (2 * ℓ)),
          IsMatrix ψ ∧ ℓ ≤ sentLen φ ∧ F (encF φ) = ℓ :: encF ψ ∧ sentLen ψ ≤ 2 * sentLen φ ∧
            ∀ (M : Type) [σ.lang.Structure M] [Nonempty M],
              (M ⊨ φ ↔ AltSat (G := Circ σ M) ψ ℓ []) := by sorry

end CoDecompFO
