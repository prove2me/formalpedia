-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_mrv_in_ch
-- name    : ApproxPolySatCH.Main.mrv_in_ch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:13:04.992738+00:00
-- url     : https://prove2.me/theorems/82116fcf-dac8-49c1-820b-a0fd7da38100
-- title:
--   Corollary 14 — Both MRV languages in CH
-- statement:
--   Both exact multivariate resultant valuation languages belong to the ordinary counting hierarchy:
--   $$\mathrm{MRV}_{\mathbb Q}\in CH,\qquad\mathrm{MRV}_{\mathrm{fin}}\in CH.$$
--   The finite-field input contains its prime and monic irreducible defining polynomial. Forms have specified positive homogeneous degrees, sparse binary exponents and a distinguished monomial. Acceptance means its coefficient has valuation strictly above the minimum valuation of all resultant coefficients. A zero resultant is a no instance. A fixed finite hierarchy level and actual finite machines precede all inputs.
--
--   This supplies the second direct input to the main theorem.
--
--   Differences from the source:
--   - encoding: Both MRV languages, including zero resultants as no instances. → Minima of finite nonzero coefficient supports in naturals with infinity, using the first parameter as epsilon.; reason: These polynomial epsilon valuations are integral, and empty-support minima are infinity, so the source strict test is preserved.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Corollary 14, p.26 (PDF p.26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=26

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem mrv_in_ch : InCH (MRV .rational) ∧ InCH MRVFinite := by sorry

end ApproxPolySatCH.Main
