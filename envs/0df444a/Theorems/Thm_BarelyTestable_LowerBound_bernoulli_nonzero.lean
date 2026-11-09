-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_bernoulli_nonzero
-- name    : BarelyTestable.LowerBound.bernoulli_nonzero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:12.117527+00:00
-- url     : https://prove2.me/theorems/1a059299-b4c9-41b5-a748-3dc090afac39
-- title:
--   Claim 3.15 — nonzero mass under independent Bernoulli coordinates
-- statement:
--   Let $\ell\ge1$, let $f:\{0,1\}^\ell\to\mathbb R$ be submodular with $f(0)>0$, and let $W$ have independent coordinates with probabilities $q_i\in[0,1]$. Then
--
--   $$\Pr[f(W)\ne0]\ge\min_{i\in[\ell]}\min(q_i,1-q_i).$$
--
--   The probabilities may differ by coordinate, and zero and one are allowed. This gives a lower bound on the support of a real submodular function without imposing a global sign condition.
--
--   Differences from the source:
--   - encoding: Boolean vectors with coordinates numbered from 1 → finite subsets of Fin n, numbered from 0; reason: the incidence-vector bijection preserves every vertex, union, intersection and coordinate square
--   - encoding: the law of independent Bernoulli coordinates → the exact product-weight sum over all subsets; reason: independence determines this law uniquely, so every source random vector has precisely this probability; the finite minimum initialized at one equals the stated minimum for ℓ ≥ 1
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Claim 3.15, p. 19 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Cube

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Claim 3.15, p.19: independent, nonidentical Bernoulli probabilities, including endpoints. -/
theorem bernoulli_nonzero {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (f : Oracle (Fin ℓ))
    (hf : Submodular f) (h0 : 0 < f ∅) (q : Fin ℓ → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    minBias q ≤ bernoulliProb q (fun S => f S ≠ 0) := by sorry

end BarelyTestable.LowerBound
