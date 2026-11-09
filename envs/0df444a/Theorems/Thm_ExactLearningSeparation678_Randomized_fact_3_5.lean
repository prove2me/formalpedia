-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_fact_3_5
-- name    : ExactLearningSeparation678.Randomized.fact_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:08.999114+00:00
-- url     : https://prove2.me/theorems/ca6b4fef-30c2-4aa6-b9a2-1227364a531d
-- title:
--   Fact 3.5 — independent uniform truncated evaluations
-- statement:
--   Let $t=2^m$ with $m\ge2$, and sample $a_0,\ldots,a_{t-1}$ independently and uniformly in $F=\mathbb F_{t^6}$. For the monic polynomial $P(X)=X^t+\sum_{j=0}^{t-1}a_jX^j$, every $r\le t$ and every list of $r$ distinct points $y_1,\ldots,y_r\in F$ satisfy
--   $$(P_{\rm trunc}(y_1),\ldots,P_{\rm trunc}(y_r))\ \sim\ \operatorname{Unif}((\mathbb F_2^{2m})^r).$$
--   Thus the evaluations are independent and individually uniform. The empty list is included with its unique distribution.
--
--   This specifies the precise independence property of the actual random polynomial, rather than existence of some unrelated hash family.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Fact 3.5, p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction
import Definitions.Def_ExactLearningSeparation678_Randomized_Observations

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Fact 3.5, p.19: joint uniformity is independence plus uniformity of every evaluation. -/
theorem fact_3_5 (m : Size) (r : ℕ) (hr : r ≤ t m) (ys : Fin r → F m)
    (hys : Function.Injective ys) :
    (PMF.uniformOfFintype (Coeff m)).map (fun a i => pTrunc m a (ys i)) =
      PMF.uniformOfFintype (Fin r → Label m) := by sorry

end ExactLearningSeparation678.Randomized
