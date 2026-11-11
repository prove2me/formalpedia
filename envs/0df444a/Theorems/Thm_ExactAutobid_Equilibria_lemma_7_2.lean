-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_lemma_7_2
-- name    : ExactAutobid.Equilibria.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:24.765199+00:00
-- url     : https://prove2.me/theorems/db1839b0-9404-4e78-8c81-4a7b1c94f2b2
-- title:
--   Lemma 7.2 — exact throttling arithmetic: Table 4 implements C, D, H, I, G under encoding (7.4)
-- statement:
--   Let $\kappa = 1/32$ and let each row of Table 4 be the budget-response system $\theta = B/\max\{B, P\}$ of its auxiliary bidders and of an output bidder with budget one. Under the encoding (7.4) of $x \in [0,1]$ by the absence probability $q = 1/(2(1+x))$ and participation probability $\theta = (1+2x)/(2(1+x))$, the rows implement
--   $$C(x) = 1-x,\quad D(x) = \min\{2x,1\},\quad H(x) = \tfrac{x}{2},\quad I(x) = \tfrac{1}{1+x},\quad G(x,y) = \min\Big\{\tfrac{1+x+y}{2}, 1\Big\}:$$
--   for encoded inputs every solution of the responses has output $\theta_{\mathrm{out}} = (1+2f)/(2(1+f))$. For arbitrary input absence probabilities in $[0,1]$ the output odds $r = (1-\theta_{\mathrm{out}})/\theta_{\mathrm{out}}$ are at most one, and at least $1/3$ when all input absence probabilities are at most $1/2$. The successive budget responses determine the auxiliary and output probabilities uniquely for fixed inputs, and every encoded input extends to the required encoded output.
--
--   These are the arithmetic gadgets of the throttling reduction (alternative (ii) of Theorem 3.1).
--
--   Differences from the source:
--   - encoding: Table 4 implements C, D, H, I, G under encoding (7.4) → ThrottleSystem.ImplementsEncoded for sysC, sysD, sysH, sysI, sysG: encoded identity θ_out = encTheta(f x) for every solution at encoded inputs, the odds ranges, ∃! solution for inputs in [0,1]^k, and existence at encoded inputs; reason: the four claims of the lemma for each row
--   - encoding: output odds r = q/θ → odds θ = (1 − θ)/θ; reason: q = 1 − θ
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 52 (PDF 54), Lemma 7.2 and Table 4

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_Throttling

namespace ExactAutobid.Equilibria

/-- **Lemma 7.2 (Exact throttling arithmetic).** Table 4 implements `C(x) = 1 − x`,
`D(x) = min{2x, 1}`, `H(x) = x/2`, `I(x) = 1/(1 + x)` and `G(x, y) = min{(1 + x + y)/2, 1}` under
encoding (7.4); output odds are at most one for arbitrary input absence probabilities in `[0, 1]`
and at least `1/3` when all of them are at most `1/2`; successive budget responses uniquely
determine the auxiliary and output probabilities for fixed inputs and extend every encoded input to
the required encoded output. -/
theorem lemma_7_2 :
    sysC.ImplementsEncoded (fun x => 1 - x 0) ∧
    sysD.ImplementsEncoded (fun x => min (2 * x 0) 1) ∧
    sysH.ImplementsEncoded (fun x => x 0 / 2) ∧
    sysI.ImplementsEncoded (fun x => 1 / (1 + x 0)) ∧
    sysG.ImplementsEncoded (fun x => min ((1 + x 0 + x 1) / 2) 1) := by sorry

end ExactAutobid.Equilibria
