-- Prove2me | Theorems.Thm_DiazModulus_isAlgebraic_of_mem_of_isAlgebraic_adjoin_transcendental
-- name    : DiazModulus.isAlgebraic_of_mem_of_isAlgebraic_adjoin_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T17:47:18.015992+00:00
-- url     : https://prove2.me/theorems/4f4c64ae-59ba-4efa-ae91-940fc9eda9b0
-- title:
--   If w is transcendental over a subfield F of ℂ, every element of F that is algebraic over ℚ(w) is algebraic over ℚ
-- statement:
--   Let $F$ be a subfield of $\mathbb{C}$, let $w \in \mathbb{C}$ be transcendental over $F$, and let $z \in F$ be algebraic over the field $\mathbb{Q}(w)$. Then $z$ is algebraic over $\mathbb{Q}$.
--
--   **Proof.** Suppose $z$ is transcendental over $\mathbb{Q}$. Since $\mathbb{Q}[z] \subseteq F$, $w$ is transcendental over $\mathbb{Q}[z]$, so the pair $(w, z)$ is algebraically independent over $\mathbb{Q}$, and so is $(z, w)$. Read the other way round, this makes $z$ transcendental over $\mathbb{Q}[w]$, hence over $\mathbb{Q}(w)$, a contradiction.
--
--   **Novelty.** A standard fact of field theory; routine.
-- source:
--   Standard field theory. R19 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem isAlgebraic_of_mem_of_isAlgebraic_adjoin_transcendental
    (F : Subfield ℂ) (w z : ℂ) (hw : Transcendental F w) (hz : z ∈ F)
    (h : IsAlgebraic (IntermediateField.adjoin ℚ ({w} : Set ℂ)) z) :
    IsAlgebraic ℚ z := by
  sorry

end DiazModulus
