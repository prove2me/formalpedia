-- Prove2me | Theorems.Thm_CoDecompFO_lemma_5_16
-- name    : CoDecompFO.lemma_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:26.777197+00:00
-- url     : https://prove2.me/theorems/31f42472-4ed1-42b7-8408-ad10d6363304
-- title:
--   Lemma 5.16 (corrected: families non-empty at every level) — sentences and induced hypotheticals
-- statement:
--   Let $G$ be a structure and $\psi$ a matrix on $[2\ell]$. Then
--   $$
--   G\models\forall x_1\exists y_1\cdots\forall x_\ell\exists y_\ell\;\psi(\vec x,\vec y)
--   $$
--   if and only if there is an induced $\ell$-hypothetical, with non-empty families at every level, all of whose hypotheses satisfy $\psi$.
--
--   This rewrites truth of the sentence as a statement about hypotheticals.
--
--   Differences from the source:
--   - correction: an induced ℓ-hypothetical, under ¶5.12's powerset, which allows empty families (¶5.8, ¶5.25) → an induced ℓ-hypothetical with non-empty families at every level; reason: the printed form is false: on a one-point G with ψ = ⊥, the hypothetical with the empty family is vacuously induced and all its hypotheses satisfy ψ, yet G ⊭ ∀x∃y ⊥
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.16, p.20; ¶5.9, p.19; ¶5.15, p.20

import Mathlib
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Lemma 5.16**, with non-empty families (Bumpus et al., arXiv:2611.04658, held file sha256
d550d7af…, p.20): "Let G be a structure and φ = ∀x₁∃y₁ …∀x_ℓ∃y_ℓ ψ(x⃗,y⃗) a formula in ∀∃-alternating
prenex normal form. Then G ⊨ φ if and only if there is an induced ℓ-hypothetical all whose hypotheses
satisfy ψ."

**Formalization Note** The induced hypothetical must have non-empty families at every level. Under
¶5.12's `P` (¶5.8: "the powerset"; ¶5.25: "we allow S = ∅") the printed statement fails: on a one-point
`G` with `ψ = ⊥`, the hypothetical with the empty family at the point is induced (¶5.15, vacuously) and
all its hypotheses satisfy `ψ`, yet `G ⊭ ∀x∃y ⊥`. `AltSat` is the sentence (see its docstring). -/
theorem lemma_5_16 {σ : Sig} (G : Type) [σ.lang.Structure G] (ℓ : ℕ)
    (ψ : σ.lang.BoundedFormula Empty (2 * ℓ)) (hψ : IsMatrix ψ) :
    AltSat (G := G) ψ ℓ [] ↔
      ∃ H : HTh σ G (2 * ℓ) ℓ, IsInducedTotal σ (2 * ℓ) ℓ [] H ∧ AllHyp ψ ℓ H := by sorry

end CoDecompFO
