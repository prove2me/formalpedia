-- Prove2me | Theorems.Thm_DualCoppersmith_Recovery_first_vector_bound
-- name    : DualCoppersmith.Recovery.first_vector_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T02:54:34.127174+00:00
-- url     : https://prove2.me/theorems/565081a9-7329-41f0-9b78-5a7bc50eaa41
-- title:
--   Lemma 2.2 — LLL first-vector bound
-- statement:
--   Let $L\subseteq\mathbb R^n$ be a rank-$n$ lattice with $n\ge1$, let an input family be a genuine basis of $L$, and let $b_1,\ldots,b_n$ be the output of a certified LLL call. For any valid certified $\delta\ge1$, the first output vector satisfies
--
--   $$\|b_1\|\le\delta^{2(n-1)}\lambda_1(L).$$
--
--   The certificate preserves a genuine lattice basis and size reduction. It accepts independent adjacent Gram–Schmidt quality data or the routine’s external law against each nonzero lattice vector. The Gram–Schmidt branch requires a geometric derivation of the approximation bound; the external-law branch requires passing from all nonzero vectors to the minimum. The asserted minimum inequality itself is not a certificate field. This retains the source’s arbitrary valid factor and does not replace it by a standard fixed numerical factor.
--
--   **Formalization Note** The first minimum is the published Euclidean infimum-of-norms definition. Real linear independence and equality of integer spans are both explicit in the basis predicate.
--
--   Differences from the source:
--   - reading: root-Hermite factor δ, described in the introduction as a valid approximation factor → δ ≥ 1 with a certificate from adjacent Gram–Schmidt lengths or the routine’s external approximation law against every nonzero lattice vector; reason: the introduction, printed p. 1, specifies a valid factor; the external-law alternative retains every valid δ even when a Gram–Schmidt test is conservative, and no target-root property is certified
--   - encoding: the smallest radius containing the required independent lattice vectors → the infimum of nonnegative qualifying radii, with the published infimum-of-norms definition for λ₁; reason: full rank and discreteness ensure nonempty radius sets, boundedness below and attainment in every theorem use
--   - encoding: the first vector b₁ of a one-based rank-d basis → output at index zero of a Fin n basis; reason: the finite basis is reindexed without changing the lattice or any bound
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 3, Lemma 2.2 (PDF p. 4); p. 1, valid approximation convention (PDF p. 2)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Geometry

set_option autoImplicit false

namespace DualCoppersmith.Recovery

open LLLFactor.RedBasis

/-- Lemma 2.2, printed p. 3 / PDF p. 4. Derive the shortest-vector bound
    from the geometric or external pointwise certificate at every valid δ. -/
theorem first_vector_bound {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
    (input output : Fin n → Vec n) (hinput : IsBasisFor input L)
    (delta : ℝ) (hdelta : 1 ≤ delta) (hcall : IsLLLCall delta input output) :
    ‖output ⟨0, hn⟩‖ ≤ delta ^ (2 * (n - 1)) * RegevLWE.SmoothingLB.lambda1 L := by sorry

end DualCoppersmith.Recovery
