-- Prove2me | Theorems.Thm_DynHaussler_lemma_9
-- name    : DynHaussler.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:21.432982+00:00
-- url     : https://prove2.me/theorems/51855605-0578-45c7-9d18-bd7d62643eeb
-- title:
--   Lemma 9 — uniformly separated reduction: a maximal $\eta$-separated subclass $H\subseteq F$
-- statement:
--   Let $X$ be a nonempty set, $F\subseteq[0,1]^X$ a nonempty class and $\eta>0$. Then there is a nonempty subclass $H\subseteq F$ such that
--   $$
--   \|h-h'\|_\infty>\eta\quad(h\neq h',\ h,h'\in H),\qquad \forall f\in F\ \exists h\in H:\ \|f-h\|_\infty\le\eta, \tag{30}
--   $$
--   and moreover $\mathrm{sfat}_\eta(H)\le\mathrm{sfat}_\eta(F)$.
--
--   The lemma reduces the upper bound to uniformly separated classes, chosen independently of the instance sequence; this is the first step of the proof of Theorem 5.
--
--   **Formalization Note** $\|h-h'\|_\infty>\eta$ is "some $x$ has $|h(x)-h'(x)|>\eta$" and $\|f-h\|_\infty\le\eta$ is "$|f(x)-h(x)|\le\eta$ for every $x$".
--
--   Differences from the source:
--   - encoding: ‖h − h′‖∞ > η and ‖f − h‖∞ ≤ η → ∃ x, η < |h x − h′ x| and ∀ x, |f x − h x| ≤ η; reason: a supremum exceeds η exactly when some term does, and is at most η exactly when every term is
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 9, Eq. (30), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

/-- **Lemma 9 (Uniformly separated reduction).** For every nonempty `F ⊆ [0,1]^X` and every
`η > 0`, there is a nonempty subclass `H ⊆ F` such that `‖h − h'‖_∞ > η` for distinct
`h, h' ∈ H`, and `∀ f ∈ F ∃ h ∈ H : ‖f − h‖_∞ ≤ η` (Eq. (30)). Moreover,
`sfat_η(H) ≤ sfat_η(F)`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Lemma 9, Eq. (30), p.17 (PDF p.19).

**Formalization Note** `‖h − h'‖_∞ > η` is `∃ x, η < |h x − h' x|` (a supremum exceeds `η`
exactly when some term does), and `‖f − h‖_∞ ≤ η` is `∀ x, |f x − h x| ≤ η`. The domain `X` is
nonempty (the paper's standing assumption, Section 3). -/
theorem lemma_9 {X : Type*} [Nonempty X] (F : Set (X → ℝ)) (hF : F.Nonempty)
    (hF01 : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) :
    ∃ H ⊆ F, H.Nonempty ∧
      (∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∃ x, η < |h x - h' x|) ∧
      (∀ f ∈ F, ∃ h ∈ H, ∀ x, |f x - h x| ≤ η) ∧
      NondualOpt.sfat H η ≤ NondualOpt.sfat F η := by sorry

end DynHaussler
