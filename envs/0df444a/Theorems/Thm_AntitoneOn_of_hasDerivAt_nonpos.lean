-- Prove2me | Theorems.Thm_AntitoneOn_of_hasDerivAt_nonpos
-- name    : AntitoneOn.of_hasDerivAt_nonpos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T16:29:24.252+00:00
-- url     : https://prove2.me/theorems/3e82f007-ce2c-452f-a32e-8fb9de9841a3
-- title:
--   A nonpositive derivative on a closed interval makes the function antitone there
-- statement:
--   Let $f,g\colon\mathbb R\to\mathbb R$ and let $a\le b$ be real. Suppose that at every point
--   $x$ of the closed interval $[a,b]$ the function $f$ is differentiable with derivative $g(x)$,
--   and that
--
--   $$
--   g(x) \;\le\; 0 \qquad \text{for every } x\in[a,b].
--   $$
--
--   Then $f$ is monotone decreasing on $[a,b]$: $f(y)\le f(x)$ whenever $x\le y$ both lie in
--   $[a,b]$.
--
--   This is the mirror of the statement for a nonnegative derivative, and it is worth having
--   separately for the same reason: the hypothesis is `HasDerivAt` at every point of the closed
--   interval, which is what differentiating an explicit formula hands you, rather than continuity
--   on the closed interval plus a condition on the interior. The two together cover the usual
--   "differentiate and read off the sign" argument in both directions. Five accepted proofs in
--   this collection each establish this one inline.
--
--   **Formalization Note.** `hd` is `HasDerivAt f (g x) x` for `x ∈ Icc a b` and `hg` is `g x ≤ 0`
--   on the same set. `AntitoneOn f (Icc a b)` is the conclusion; `a ≤ b` is not assumed.
-- source:
--   Five distinct accepted submissions prove this inline, each for itself. Carved from https://prove2.me/submissions/108d25ac-4cbb-466b-9bd4-122188ee844b, lines 94-104.

import Mathlib

open Set

theorem AntitoneOn.of_hasDerivAt_nonpos {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, g x ≤ 0) : AntitoneOn f (Icc a b) := by sorry
