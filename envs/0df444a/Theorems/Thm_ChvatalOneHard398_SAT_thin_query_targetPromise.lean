-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_thin_query_targetPromise
-- name    : ChvatalOneHard398.SAT.thin_query_targetPromise
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:21:05.46429+00:00
-- url     : https://prove2.me/theorems/09b30b51-bccf-4df5-9b5f-790829c80cdf
-- title:
--   Thin constructed formulas satisfy the target promise
-- statement:
--   Every thin formula produced by the residue construction of Proposition 16 satisfies the promise used as the target of Theorem C. Explicitly, if $F=F(p,h,H,D,t)$ for valid parameters and
--
--   $$
--   \lambda_1\bigl(\Lambda_D^\perp(H)\bigr)>
--    m^{3/2}p_{\max}(2^h-1)/2,
--   $$
--
--   then $F$ is well formed, every clause has at most three literals, and its SAT polytope satisfies $P(F)'=P(F)_I$. Proposition 16 in fact gives the stronger hereditary conclusion for every rational subpolyhedron; this implication records only the part needed by Theorem C.
--
--   **Formalization Note** `ThinQuery` also fixes the formula to the explicit map `latticeFormula`; `TargetPromise` includes nonemptiness and range checks through `Formula.WellFormed`.
-- source:
--   Alberto Del Pia, STOC 2027 submission #398, p.18 Proposition 16(a,b), p.17 definition of the SAT polytope, and p.29 proof of Theorem C; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

theorem ChvatalOneHard398.SAT.thin_query_targetPromise (F : ChvatalOneHard398.SAT.Formula) : ChvatalOneHard398.SAT.ThinQuery F → ChvatalOneHard398.SAT.TargetPromise F := by sorry
