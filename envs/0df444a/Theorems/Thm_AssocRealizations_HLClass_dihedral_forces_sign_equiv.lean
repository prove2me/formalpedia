-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_dihedral_forces_sign_equiv
-- name    : AssocRealizations.HLClass.dihedral_forces_sign_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:15.290985+00:00
-- url     : https://prove2.me/theorems/4079136f-ed7b-4e57-977a-4b87ca6c4d57
-- title:
--   Proof of Theorem 4.9, p. 18 — a dihedral symmetry preserving parallel pairs is a reflection-reversal of the sign sequence
-- statement:
--   Let $\sigma_1, \sigma_2 \in \{+,-\}^{n-1}$ and let $g$ be a dihedral symmetry of the $(n+3)$-gon (a rotation $i \mapsto r+i$ or a reflection $i \mapsto r-i$ of the positions) such that, for all diagonals $\delta, \delta'$,
--   $$v_\delta(\sigma_1),\ v_{\delta'}(\sigma_1) \text{ are opposite} \iff v_{g(\delta)}(\sigma_2),\ v_{g(\delta')}(\sigma_2) \text{ are opposite}.$$
--   Then $\sigma_2$ can be obtained from $\sigma_1$ by reflections and reversals: $\sigma_2 \in \{\sigma_1, -\sigma_1, \sigma_1^t, -\sigma_1^t\}$.
--
--   This is the conclusion of the "only if" direction of Theorem 4.9: a symmetry of the polygon that maps the parallel pairs of $P_{n+3}(\sigma_1)$ onto those of $P_{n+3}(\sigma_2)$ corresponds to a reflection-reversal of the sign word $\widetilde\sigma_1 = \{+,-,\sigma_1,-,+\}$.
--
--   **Formalization Note** $g$ acts on the positions of the polygon, which carry the labels of $P_{n+3}(\sigma_1)$ on one side and those of $P_{n+3}(\sigma_2)$ on the other.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 18, proof of Theorem 4.9, first paragraph (end)

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Proof of Theorem 4.9 (p. 18): if a AssocRealizations.TypesMeet.dihedral symmetry `g` of the (n + 3)-gon maps the parallel
pairs of diagonals of `P_{n+3}(σ₁)` exactly onto those of `P_{n+3}(σ₂)`, then `σ₂` is obtained
from `σ₁` by reflections and reversals. -/
theorem dihedral_forces_sign_equiv (n : ℕ) (σ₁ σ₂ : Fin (n - 1) → Bool) (r : Fin (n + 3))
    (refl : Bool)
    (h : ∀ e f : Sym2 (Fin (n + 3)), IsDiagonal e → IsDiagonal f →
      (AssocRealizations.TypesMeet.Opposite (hlVec n σ₁ e) (hlVec n σ₁ f) ↔
        AssocRealizations.TypesMeet.Opposite (hlVec n σ₂ (Sym2.map (AssocRealizations.TypesMeet.dihedral r refl) e))
          (hlVec n σ₂ (Sym2.map (AssocRealizations.TypesMeet.dihedral r refl) f)))) :
    SignEquiv σ₁ σ₂ := by sorry

end AssocRealizations.HLClass
