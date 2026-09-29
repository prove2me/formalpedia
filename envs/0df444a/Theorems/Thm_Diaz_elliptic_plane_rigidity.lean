-- Prove2me | Theorems.Thm_Diaz_elliptic_plane_rigidity
-- name    : Diaz.elliptic_plane_rigidity
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:11:04.70927+00:00
-- url     : https://prove2.me/theorems/9574da25-44f3-4b8f-ae2a-61f2b55e36fa
-- title:
--   A distance-rigid locus has no collinear triple
-- statement:
--   **Source.** Carlo Perassi's theorem on elliptic algebraic distance and plane rigidity, from a transfer of his argument to elliptic curves — its second half, the plane statement; unpublished apart from this node.
--
--   **Statement, as formalised.** Let `k ⊆ ℂ` be a subfield of algebraic numbers and `D ⊆ ℂ` a
--   set such that
--
--   * every `x ∈ D` has algebraic norm `x conj x`;
--   * `D` is stable under multiplication by `k^×`;
--   * (*distance dichotomy*) distinct `x, y ∈ D` with `(x−y) conj (x−y)` algebraic satisfy
--     `y ∈ k^× x`.
--
--   If `u, v, w ∈ D` with `v ∉ k u`, and `w = a u + b v` with `a, b ∈ k`, then `a = 0` or
--   `b = 0`. Equivalently: `D ∩ span_k{u,v} = k^× u ⊔ k^× v`, so the image of `D` in the
--   projective space has no collinear triple.
--
--   **What is a hypothesis and why.** In the theorem, `D` is the elliptic Diaz locus, `k` the
--   endomorphism field, and the distance dichotomy is the *first* half of the same theorem. That
--   first half splits in two: an identity of quadratic algebras — the cosine rule, published on
--   this mission as `Diaz.trace_norm_quadratic_algebra` and `Diaz.quadratic_algebra_distance`,
--   which give `u conj v` algebraic and hence `u/v` algebraic — and then the **elliptic Baker
--   theorem** of Masser and Bertrand–Masser, which converts an algebraic linear relation between
--   elliptic logarithms into a `k`-linear one. Elliptic Baker is not in Mathlib and is not
--   formalisable here, so it is carried as the explicit hypothesis `hdist`, together with the
--   consequence of it that the theorem's proof uses a second time in the plane argument (the reduction
--   of `w` to a `k`-combination of `u` and `v`, which appears here as the hypothesis that `w` has
--   that shape). The citation boundary is therefore visible in the statement itself.
--
--   The one step that is *not* a citation is what is proved: if `ab ≠ 0` then `a u ∈ D`,
--   `w ≠ a u`, and `(w − a u) conj (w − a u) = b conj b · v conj v` is algebraic because
--   `b conj b` is a product of algebraic numbers — in the elliptic setting, because `|b|² = N(b) ∈ ℚ`.
--   The dichotomy applied to `a u` and `w` then puts `w` in `k^× (a u)`, whence `v ∈ k^× u`,
--   contradicting independence.
--
--   **No new definition.** `ℒ_E` and the elliptic Diaz locus do not appear; `D` is an arbitrary
--   set with the three stated closure properties.
--
--   **Not in the companion note.** This statement is not in Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). It was left out for scope: the note treats the Diaz locus, not the consequences of the same machinery for
--   all logarithms or the transfers to elliptic and p-adic settings. Nothing
--   was withdrawn as wrong: the transfers were moved out, not retracted.
--
--   **Novelty.** No novelty is claimed, either for the mathematics or for the formalisation.
--   Carlo Perassi presents these statements as transfers of a complex argument to
--   another setting.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.elliptic_plane_rigidity {k : Subfield ℂ} (D : Set ℂ)
    (hkalg : ∀ γ ∈ k, IsAlgebraic ℚ γ)
    (hnorm : ∀ x ∈ D, IsAlgebraic ℚ (x * conj x))
    (hstab : ∀ x ∈ D, ∀ γ ∈ k, γ ≠ 0 → γ * x ∈ D)
    (hdist : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      IsAlgebraic ℚ ((x - y) * conj (x - y)) → ∃ γ ∈ k, y = γ * x)
    {u v w : ℂ} (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D)
    (hind : ∀ γ ∈ k, v ≠ γ * u)
    {a b : ℂ} (ha : a ∈ k) (hb : b ∈ k) (hrep : w = a * u + b * v) :
    a = 0 ∨ b = 0 := by sorry
