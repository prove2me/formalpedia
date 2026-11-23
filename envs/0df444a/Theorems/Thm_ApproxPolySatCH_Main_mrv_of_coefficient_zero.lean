-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_mrv_of_coefficient_zero
-- name    : ApproxPolySatCH.Main.mrv_of_coefficient_zero
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:27:40.369459+00:00
-- url     : https://prove2.me/theorems/47297a02-47c6-439c-a6b0-e62ba4a3e442
-- title:
--   Corollary 14 (fixed field) — MRV from resultant coefficient tests
-- statement:
--   Fix a rational or finite coefficient field $k$. If exact vanishing of a specified sparse multihomogeneous resultant coefficient is decidable in the counting hierarchy, then the multivariate resultant valuation language over $k$ is also in the counting hierarchy:
--   $$
--   \operatorname{CoefficientZero}_k\in CH\quad\Longrightarrow\quad \operatorname{MRV}_k\in CH.
--   $$
--
--   Write the resultant as $R(\varepsilon,Y)=\sum_{\beta,j}c_{\beta,j}\varepsilon^jY^\beta$, with distinguished exponent tuple $\beta_0$. The strict valuation inequality is equivalent to
--   $$
--   \exists\beta\,\exists j\;\Bigl(c_{\beta,j}\ne0\;\wedge\;
--     \forall j'\le j,\;c_{\beta_0,j'}=0\Bigr).
--   $$
--   The nonzero test is the negation of a coefficient-zero test. Standard resultant degree bounds make all relevant binary exponent addresses polynomially bounded, so the fixed bounded existential--universal construction remains in CH. This includes zero resultants and empty supports: an identically zero $R$ has no witness and is rejected, while an empty distinguished support has order $+\infty$.
--
--   The field, hierarchy level, finite machines and polynomial clocks are fixed before the encoded input; malformed words are outside the language.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), equation (10), pp.13–14, and proof of Corollary 14, p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=26

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- The bounded existential--universal coefficient test in the proof of Corollary 14. -/
theorem mrv_of_coefficient_zero (k : CoefficientField) :
    InCH (CoefficientZero k) → InCH (MRV k) := by sorry
