-- Prove2me | Theorems.Thm_DynHaussler_lemma_10
-- name    : DynHaussler.lemma_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:35:18.471192+00:00
-- url     : https://prove2.me/theorems/930dfc52-a626-436d-b3d1-e6aaa3edda59
-- title:
--   Lemma 10 — rank-zero classes have oscillation at most $\eta$; separated ones are singletons
-- statement:
--   Let $\eta>0$ and let $\emptyset\neq V\subseteq[0,1]^X$ have rank zero, $\mathrm{sfat}_\eta(V)=0$. Then
--   $$
--   \sup_{f\in V}f(x)-\inf_{f\in V}f(x)\le\eta\qquad(x\in X). \tag{31}
--   $$
--   If, in addition, $V$ is a subclass of a class $H$ whose distinct members satisfy $\|h-h'\|_\infty>\eta$, then $V$ is a singleton.
--
--   The lemma gives the $d=0$ case of Proposition 2 and of Theorem 5 (one expert suffices).
--
--   **Formalization Note** The supremum and infimum range over the members of $V$; they are finite because $V$ is nonempty and $[0,1]$-valued.
--
--   Differences from the source:
--   - generalization: the scale η of Section 4 satisfies 0 < η < 1 (fixed with the hypotheses of Proposition 2) → only 0 < η is assumed; reason: the proof never uses η < 1; every instance with η < 1 is an instance of the Lean statement
--   - encoding: ‖h − h′‖∞ > η and ‖f − h‖∞ ≤ η → ∃ x, η < |h x − h′ x| and ∀ x, |f x − h x| ≤ η; reason: a supremum exceeds η exactly when some term does, and is at most η exactly when every term is
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 10, Eq. (31), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 10 (Rank-zero classes).** If `∅ ≠ V ⊆ [0,1]^X` has rank zero (`sfat_η(V) = 0`), then
`sup_{f ∈ V} f(x) − inf_{f ∈ V} f(x) ≤ η` for every `x ∈ X` (Eq. (31)). If, in addition, `V` is a
subclass of a uniformly greater-than-`η` separated class, then `V` is a singleton.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 10, Eq. (31), p.18 (PDF p.20); the scale `η > 0` is fixed in Section 4.1.

**Formalization Note** The supremum and infimum are `⨆` and `⨅` over the subtype `V`, which is
nonempty and whose values at `x` lie in `[0,1]`, so both are the genuine sup and inf. "Uniformly
greater-than-`η` separated" is `∀ h h' ∈ H, h ≠ h' → ∃ x, η < |h x − h' x|`
(`‖h − h'‖_∞ > η`). Section 4.1 also has `η < 1`; it is not assumed here. -/
theorem lemma_10 {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (V : Set (X → ℝ))
    (hV : V.Nonempty) (hV01 : ∀ f ∈ V, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hrank : NondualOpt.sfat V η = 0) :
    (∀ x : X, (⨆ f : V, (f : X → ℝ) x) - (⨅ f : V, (f : X → ℝ) x) ≤ η) ∧
      (∀ H : Set (X → ℝ), V ⊆ H →
        (∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∃ x, η < |h x - h' x|) → ∃ f, V = {f}) := by sorry

end DynHaussler
