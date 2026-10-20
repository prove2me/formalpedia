-- Prove2me | Theorems.Thm_ContestDuration_Patient_scale_identities
-- name    : ContestDuration.Patient.scale_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:38.313548+00:00
-- url     : https://prove2.me/theorems/3b1fd7de-8834-424d-8414-ccb9dc42f64c
-- title:
--   Equations (18)–(19) — scaling the shock changes the maximum and incentives
-- statement:
--   Let $h_\alpha(s)=h(s/\alpha)/\alpha$ for $\alpha>0$, with $h$ the contest's mean-zero log-concave shock density. Its cumulative distribution is $H_\alpha(s)=H(s/\alpha)$. The expected maximum and marginal rank probabilities obey
--
--   $$E_N(h_\alpha)=\alpha E_N(h),\qquad I_j^N(h_\alpha)=I_j^N(h)/\alpha,\qquad x(h_\alpha)=x(h)/\alpha.$$
--
--   These identities express equations (18) and (19) using the density transformed by the scale parameter. They are the quantitative link between agent uncertainty and optimal duration.
--
--   **Formalization Note** The rank identity is stated for $j=1,\ldots,N$. Each transformed quantity is computed from $h_\alpha$; none is an independent parameter.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 9, scale transformation; p. 27, proof of Theorem 1(a), equations (18)–(19)

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

open CrowdContest.Pooling (cdf)

namespace ContestDuration.Patient

theorem scale_identities (P : Params) (hS : P.Standing) (h : ℝ → ℝ)
    (hh : ShockOK h) (α : ℝ) (hα : 0 < α) :
    (∀ s, cdf (scaled h α) s = cdf h (s / α)) ∧
    CrowdContest.Pooling.expMax (scaled h α) P.N =
      α * CrowdContest.Pooling.expMax h P.N ∧
    (∀ j ∈ Finset.Icc 1 P.N, Irank P.N j (scaled h α) = Irank P.N j h / α) ∧
    xOf P (scaled h α) = xOf P h / α := by sorry

end ContestDuration.Patient
