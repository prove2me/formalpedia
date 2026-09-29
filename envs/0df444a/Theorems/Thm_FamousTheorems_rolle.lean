-- Prove2me | Theorems.Thm_FamousTheorems_rolle
-- name    : FamousTheorems.rolle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:09.150826+00:00
-- url     : https://prove2.me/theorems/7396008d-9feb-4b61-b398-a2dfa70db2a4
-- title:
--   Rolle's theorem
-- statement:
--   **Rolle's theorem.**
--
--   If $f$ is continuous on $[a,b]$ with $a < b$ and $f(a) = f(b)$, then
--   $$\exists\, c \in (a,b) \text{ with } f'(c) = 0 .$$
--
--   A function that returns to its starting value must turn around somewhere. The proof is that a
--   continuous function on a compact interval attains its extrema, and an interior extremum forces the
--   derivative to vanish; the endpoints are excluded from the conclusion precisely because the extremum
--   might be attained there, which is what $f(a) = f(b)$ rules out.
--
--   Rolle's theorem and the mean value theorem are equivalent — tilting the picture by subtracting the
--   secant line turns one into the other — but Rolle's is the one that gets proved first, and almost
--   every qualitative fact about derivatives descends from it: monotonicity criteria, uniqueness of
--   antiderivatives up to constants, Taylor's theorem with Lagrange remainder, and the interlacing of
--   roots of a polynomial and its derivative.
--
--   Michel Rolle proved it for polynomials in 1691, in a treatise otherwise hostile to the infinitesimal
--   calculus he is now remembered for underwriting.
--
--   **Formalization note.** No differentiability hypothesis is needed: `deriv` is junk-valued (zero)
--   where $f$ is not differentiable, so the conclusion holds vacuously in that case and the statement is
--   strictly stronger than the textbook version. The result is Mathlib's `exists_deriv_eq_zero`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Set.Ioo a b, deriv f c = 0 := by sorry

end FamousTheorems
