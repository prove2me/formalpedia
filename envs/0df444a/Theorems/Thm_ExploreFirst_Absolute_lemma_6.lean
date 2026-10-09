-- Prove2me | Theorems.Thm_ExploreFirst_Absolute_lemma_6
-- name    : ExploreFirst.Absolute.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:22.478977+00:00
-- url     : https://prove2.me/theorems/0f9091d4-0695-4b1e-9a1d-8876f26aff0d
-- title:
--   Lemma 6 — local refinement of Pinsker's inequality
-- statement:
--   For Bernoulli parameters $0\le p<q\le1$, let $M=\max_{x\in[p,q]}x(1-x)$. Then
--   $$\mathrm{kl}(p,q)\ge\frac{(p-q)^2}{2M}\ge\frac{(p-q)^2}{2q}.$$
--
--   This local refinement retains the interval-dependent factor used in the small-horizon bound. It includes $p=0$ and $q=1$, where the divergence may be infinite.
--
--   **Formalization Note** The maximum is encoded by the supremum of the image of the nonempty compact interval $[p,q]$; its value is positive because $p<q$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 20, Lemma 6

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

namespace ExploreFirst.Absolute

/-- Garivier–Ménard–Stoltz, Lemma 6, p. 20. -/
theorem lemma_6 (p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    ENNReal.ofReal ((p - q) ^ 2 /
      (2 * sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q))) ≤ ExploreFirst.FundIneq.klBer p q ∧
    (p - q) ^ 2 / (2 * q) ≤
      (p - q) ^ 2 / (2 * sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q)) := by sorry

end ExploreFirst.Absolute
