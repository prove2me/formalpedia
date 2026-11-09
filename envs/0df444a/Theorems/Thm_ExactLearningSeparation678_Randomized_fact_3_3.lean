-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_fact_3_3
-- name    : ExactLearningSeparation678.Randomized.fact_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:19.644193+00:00
-- url     : https://prove2.me/theorems/12d8db19-9f5f-4b99-9fb3-e94c44f4cb54
-- title:
--   Fact 3.3 — polynomial fiber bound and nonconstancy
-- statement:
--   Let $t=2^m$ with $m\ge2$, and let $P(X)=X^t+\sum_{j=0}^{t-1}a_jX^j$ have arbitrary coefficients in $F=\mathbb F_{t^6}$. Put $P_{\rm trunc}=\operatorname{trunc}\circ P$. Then
--   $$\forall z\in\mathbb F_2^{2m},\quad |P_{\rm trunc}^{-1}(z)|\le t^5,$$
--   and $P_{\rm trunc}$ is nonconstant.
--
--   Both the fiber bound and nonconstancy are retained: they serve distinct uses in the quantum bound and injectivity assertion.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Fact 3.3, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Fact 3.3, p.18: the full monic polynomial has bounded truncated fibers and is nonconstant. -/
theorem fact_3_3 (m : Size) (a : Coeff m) :
    (∀ z : Label m, (Finset.univ.filter (fun y => pTrunc m a y = z)).card ≤ (t m) ^ 5) ∧
    ∃ y y' : F m, pTrunc m a y ≠ pTrunc m a y'  := by sorry

end ExactLearningSeparation678.Randomized
