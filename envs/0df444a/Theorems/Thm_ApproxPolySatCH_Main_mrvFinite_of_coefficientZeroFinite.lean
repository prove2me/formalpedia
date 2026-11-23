-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_mrvFinite_of_coefficientZeroFinite
-- name    : ApproxPolySatCH.Main.mrvFinite_of_coefficientZeroFinite
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:29:20.405651+00:00
-- url     : https://prove2.me/theorems/122fae41-66df-4a7d-8f69-4f97b7b7a830
-- title:
--   Corollary 14 (finite fields) — Tagged MRV from tagged coefficient tests
-- statement:
--   For finite fields presented as $\mathbb F_p[U]/(\mu)$, with $(p,\mu)$ included in the input word, membership of the tagged resultant coefficient-zero language in CH implies membership of the tagged multivariate resultant valuation language in CH:
--   $$
--   \operatorname{CoefficientZero}_{\mathrm{fin}}\in CH
--   \quad\Longrightarrow\quad
--   \operatorname{MRV}_{\mathrm{fin}}\in CH.
--   $$
--
--   For each supplied field, the proof uses the same coefficient expansion $R(\varepsilon,Y)=\sum_{\beta,j}c_{\beta,j}\varepsilon^jY^\beta$ and the bounded criterion
--   $$
--   \exists\beta\,\exists j\;\Bigl(c_{\beta,j}\ne0\;\wedge\;
--     \forall j'\le j,\;c_{\beta_0,j'}=0\Bigr).
--   $$
--   Nonvanishing is tested by negating the corresponding zero test. The exponent bounds and finite hierarchy construction are uniform in the presented $(p,\mu)$; the field tag is copied into every coefficient query. One fixed hierarchy level and finite machines therefore handle every valid field description and every input length. Invalid tags or malformed words are rejected, and empty coefficient supports retain their $+\infty$ order convention.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 13 and proof of Corollary 14, pp.25–26, with equation (10), pp.13–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=26

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- The uniform finite-field tagged form of the bounded coefficient test in Corollary 14. -/
theorem mrvFinite_of_coefficientZeroFinite :
    InCH CoefficientZeroFinite → InCH MRVFinite := by sorry
