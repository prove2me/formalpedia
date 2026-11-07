-- Prove2me | Theorems.Thm_DynHaussler_lemma_12
-- name    : DynHaussler.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:57.643607+00:00
-- url     : https://prove2.me/theorems/5b61d3b9-c509-4a35-801e-e798ef970ad1
-- title:
--   Lemma 12 — rank-decreasing center: both sign updates have rank $\le r-1$
-- statement:
--   Let $\eta>0$, let $\emptyset\neq V\subseteq[0,1]^X$ have finite rank $r=\mathrm{sfat}_\eta(V)$, and let $x\in X$. Then the two sign-update classes
--   $$
--   V^-_x=\{f\in V: f(x)\le a(V,x)-\eta\},\qquad V^+_x=\{f\in V: f(x)\ge a(V,x)+\eta\} \tag{33}
--   $$
--   have rank at most $r-1$, with the convention $\mathrm{sfat}_\eta(\emptyset)=-1$. Here $a(V,x)$ is the center of Eq. (32). In particular, for $r=0$ both classes are empty.
--
--   Every valid correction therefore lowers the rank, so at most $r$ corrections can occur from a class of rank $r$.
--
--   **Formalization Note** Ranks are compared in `WithBot ℕ∞`; "rank at most $r-1$" for the integer $r$ is "rank $<r$".
--
--   Differences from the source:
--   - generalization: the scale η of Section 4 satisfies 0 < η < 1 (fixed with the hypotheses of Proposition 2) → only 0 < η is assumed; reason: the proof never uses η < 1; every instance with η < 1 is an instance of the Lean statement
--   - encoding: sfat_η(∅) = −1 (integer-valued rank) → the rank wrapper `rank` in WithBot ℕ∞, with ⊥ for the empty class; reason: ⊥ plays −1; on nonempty classes rank = sfat
--   - encoding: signs − and + → Bool (false is −, true is +); reason: two-element type
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 12, Eq. (33), p.19 (PDF p.21); center (32), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DynHaussler_signUpdate

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 12 (Rank-decreasing center).** For every nonempty class `V ⊆ [0,1]^X` of finite rank
`r = sfat_η(V)` and every `x ∈ X`, the two sign-update classes
`V⁻_x = {f ∈ V : f(x) ≤ a(V, x) − η}` and `V⁺_x = {f ∈ V : f(x) ≥ a(V, x) + η}` (Eq. (33)) have
rank at most `r − 1`, with the convention `sfat_η(∅) = −1`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 12, Eq. (33), p.19 (PDF p.21); the center `a(V, x)` is Eq. (32), p.18 (PDF p.20).

**Formalization Note** Ranks are the rank wrapper `rank` in `WithBot ℕ∞` (`⊥` is `−1`), so "rank at
most `r − 1`" for the integer `r` is `rank < r`; for `r = 0` this says the class is empty. The sign
`b = true` is `V⁺_x`, `b = false` is `V⁻_x`. Section 4.1 also has `η < 1`; it is not assumed here. -/
theorem lemma_12 {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (V : Set (X → ℝ))
    (hV : V.Nonempty) (hV01 : ∀ f ∈ V, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (r : ℕ)
    (hr : NondualOpt.sfat V η = r) (x : X) (b : Bool) :
    rank η (signUpdate η V x b) < (((r : ℕ∞)) : WithBot ℕ∞) := by sorry

end DynHaussler
