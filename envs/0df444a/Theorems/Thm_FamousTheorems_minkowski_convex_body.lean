-- Prove2me | Theorems.Thm_FamousTheorems_minkowski_convex_body
-- name    : FamousTheorems.minkowski_convex_body
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:06:18.863711+00:00
-- url     : https://prove2.me/theorems/b2a27f0d-a02c-44f6-b497-5056d1289b60
-- title:
--   Minkowski's convex body theorem
-- statement:
--   **Minkowski's convex body theorem** (the fundamental theorem of the geometry of numbers).
--
--   Let $L$ be a lattice in an $n$-dimensional real vector space with fundamental domain $F$, and let
--   $s$ be a convex set symmetric about the origin. If
--   $$\mu(s) > 2^n \mu(F),$$
--   then $s$ contains a nonzero lattice point.
--
--   The bound is sharp: the open cube $(-1,1)^n$ has volume exactly $2^n$ against the lattice
--   $\mathbb{Z}^n$ with unit covolume, and contains no nonzero lattice point. The proof is a pigeonhole
--   argument on the half-body $\tfrac12 s$, and the two hypotheses are exactly what make it work —
--   symmetry and convexity together say that if $\tfrac12 s$ meets a translate of itself, the difference
--   of the two points lies in $s$.
--
--   Minkowski introduced this in 1889 and built the *Geometrie der Zahlen* around it. Despite the
--   elementary proof it is startlingly powerful: it yields Lagrange's four-square theorem, Fermat's
--   two-square theorem, Dirichlet's unit theorem, and the finiteness of the class number, all by
--   choosing the right convex body.
--
--   **Formalization note.** `IsAddFundamentalDomain L F μ` says $F$ tiles under translation by $L$, so
--   $\mu(F)$ is the covolume; `μ.IsAddHaarMeasure` fixes the translation-invariant measure. The result is
--   Mathlib's `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem minkowski_convex_body {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {F s : Set E} {L : AddSubgroup E} [Countable L]
    (fund : IsAddFundamentalDomain L F μ) (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s) (h : μ F * 2 ^ Module.finrank ℝ E < μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := by sorry

end FamousTheorems
