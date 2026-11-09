-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_lemma_3_3
-- name    : ExplicitTensorBarrier694.Explicit.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:26:34.924742+00:00
-- url     : https://prove2.me/theorems/48ba4b8f-d995-4b09-b269-2dd3b6584ffa
-- title:
--   Lemma 3.3 — sum of nullities at distinct complex points
-- statement:
--   Let $e\ge2$, $s=2e-1$, and let $f_1,\ldots,f_s$ be monic complex polynomials with pairwise distinct degrees strictly below $e^2$, as in Definition 3.2. For every nonnegative integer $L$ and every collection of pairwise distinct complex points $t_0,\ldots,t_{L-1}$,
--
--   $$\sum_{j=0}^{L-1}\dim_{\mathbb C}\ker M_f(t_j)\le e\binom{s}{e-1}(e^2-1).$$
--
--   There is no restriction to real points, powers of two, or nonzero points. The sum counts full kernel dimensions rather than merely singular matrices, and it is zero when $L=0$. This is the uniform singularity budget used for restrictions of the block tensor.
--
--   Differences from the source:
--   - encoding: indices 1 through s for polynomial and basis labels → Fin s for these labels; reason: a bijective relabeling; zero-based block indices and all powers are unchanged
--   - encoding: complex polynomials of degrees below e² → monic polynomials with natDegree<e² and an injective natDegree function; reason: monicity excludes zero, so natural degree is the ordinary degree on every source instance
--   - encoding: s=2e−1 and integer e²−1 → natural-number arithmetic under e≥2; reason: these subtractions are nonnegative on the complete source domain and hence agree with integer arithmetic
--   - encoding: Koszul flattening K_p as an abstract linear map → its matrix in increasing exterior bases z_I and the standard bases of B* and C, with sign (−1)^#{i∈I : i<l} for z_l∧z_I; reason: this is the matrix of the source map in those bases, and rank, kernel dimension and invertibility do not depend on the bases
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 3.3, p.8, equation (3.1), with Definition 3.2 p.8 and Section 3 preamble p.7 (PDF same pages); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_PolynomialFamily

open scoped BigOperators

namespace ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 3.3, p.8 (3.1).
Arbitrary finite number L (including zero) of distinct complex points. -/
theorem lemma_3_3 (e : ℕ) (he : 2 ≤ e)
    (f : Fin (2 * e - 1) → Polynomial ℂ) (hf : PolynomialData e f)
    (L : ℕ) (t : Fin L → ℂ) (ht : Function.Injective t) :
    (∑ j : Fin L, polynomialNullity f (t j)) ≤
      e * Nat.choose (2 * e - 1) (e - 1) * (e ^ 2 - 1) := by sorry

end ExplicitTensorBarrier694.Explicit
