-- Prove2me | Theorems.Thm_DynHaussler_lemma_11
-- name    : DynHaussler.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:59.134326+00:00
-- url     : https://prove2.me/theorems/e2cf291f-c5ea-41a3-b4b7-c3239cb91fb3
-- title:
--   Lemma 11 — gluing shattered trees: two rank-$\ge r$ fibers give $\mathrm{sfat}_\eta(V)\ge r+1$
-- statement:
--   Let $\eta>0$, $V\subseteq[0,1]^X$, $x\in X$ and $z_1-z_0\ge\eta$. If both classes
--   $$
--   \{f\in V: f(x)\le z_0\},\qquad \{f\in V: f(x)\ge z_1\}
--   $$
--   have rank at least an integer $r\ge0$ (with $\mathrm{sfat}_\eta(\emptyset)=-1$, so both are nonempty), then
--   $$
--   \mathrm{sfat}_\eta(V)\ge r+1 .
--   $$
--
--   This is the elementary operation behind the rank-decreasing center of Lemma 12.
--
--   Differences from the source:
--   - generalization: the scale η of Section 4 satisfies 0 < η < 1 (fixed with the hypotheses of Proposition 2) → only 0 < η is assumed; reason: the proof never uses η < 1; every instance with η < 1 is an instance of the Lean statement
--   - encoding: sfat_η(∅) = −1 (integer-valued rank) → the rank wrapper `rank` in WithBot ℕ∞, with ⊥ for the empty class; reason: ⊥ plays −1; on nonempty classes rank = sfat
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 11, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DynHaussler_rank

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 11 (Gluing shattered trees).** Let `V ⊆ [0,1]^X`, `x ∈ X`, and `z_1 − z_0 ≥ η`. If both
classes `{f ∈ V : f(x) ≤ z_0}` and `{f ∈ V : f(x) ≥ z_1}` have rank at least an integer `r ≥ 0`,
then `sfat_η(V) ≥ r + 1`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 11, p.18 (PDF p.20); the scale `η > 0` is fixed in Section 4.1.

**Formalization Note** "Rank at least `r ≥ 0`" uses the rank wrapper `rank` (`⊥` for the empty
class, the paper's `sfat_η(∅) = −1`), so it forces both classes to be nonempty. Section 4.1 also
has `η < 1`; it is not assumed here. -/
theorem lemma_11 {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (V : Set (X → ℝ))
    (hV01 : ∀ f ∈ V, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (x : X) (z₀ z₁ : ℝ) (hz : η ≤ z₁ - z₀)
    (r : ℕ) (h₀ : (((r : ℕ∞)) : WithBot ℕ∞) ≤ rank η {f ∈ V | f x ≤ z₀})
    (h₁ : (((r : ℕ∞)) : WithBot ℕ∞) ≤ rank η {f ∈ V | z₁ ≤ f x}) :
    ((r : ℕ∞) + 1) ≤ NondualOpt.sfat V η := by sorry

end DynHaussler
