-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_theorem_1
-- name    : ContiguousCake597.Approximate.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:59.410942+00:00
-- url     : https://prove2.me/theorems/815f0379-994f-471c-9776-29887651ccec
-- title:
--   Theorem 1 — full PPAD-completeness classification
-- statement:
--   Given $n\ge1$ agents with normalized nonnegative rational piecewise-constant additive valuations on $[0,1]$ and a positive rational $\varepsilon$, compute a complete contiguous allocation with rational cuts and arbitrary assignment satisfying
--   $$V_i(P_{\sigma(i)})\ge V_i(P_j)-\varepsilon\quad\text{for every agent }i\text{ and spatial piece }j.$$
--   This search problem is PPAD-complete. The classification holds for both binary and unary encodings of the positive numerator and denominator of $\varepsilon$. Hardness holds simultaneously with the restriction that every density takes only the values $\lambda$ and $2\lambda$ for one $\lambda>0$ common to all agents and has at most six genuine breakpoints. Precisely, all four relations are PPAD-complete:
--   $$\mathcal C_{\mathrm{binary,general}},\quad\mathcal C_{\mathrm{unary,general}},\quad\mathcal C_{\mathrm{binary,restricted}},\quad\mathcal C_{\mathrm{unary,restricted}}.$$
--   Completeness means totality and a uniform polynomial-time reduction to End-of-Line, together with polynomial-time search hardness for every PPAD problem. Every target answer must decode correctly. Time is measured in total bit length, including precision; $n$ is part of the input. Lemma 3 supplies verification and short-witness existence.
--
--   The hard construction has $N=32(s+1)^2$, $L=40N^2$, $\varepsilon=1/(8000N^4)$ and common $\lambda=L/(L+6)$. These fix one hardness family and do not restrict general membership instances.
--
--   Differences from the source:
--   - encoding: PPAD-completeness and the simultaneous unary and density restrictions → a conjunction of PPAD-completeness of the four precisely encoded search relations; reason: makes both precision encodings and simultaneous restrictions explicit, with no loss of instances or conclusions
--   - encoding: a positive common scale λ for rational density levels → a positive rational common scale λ; reason: normalization and nonemptiness give a positive rational level r; λ is either r or r/2, so the restricted input class is unchanged
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 1 (PDF 2), Theorem 1, proof p.11 (PDF 12)

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Theorem 1, printed p.1 (PDF 2), proof printed p.11 (PDF 12).
The four search problems use the entire encoded input length, with complete
rational-cut answers and freely chosen assignment permutations. -/
theorem theorem_1 :
    QuasiStrictNE.PPADComplete (CakeProblem .binary false) ∧
    QuasiStrictNE.PPADComplete (CakeProblem .unary false) ∧
    QuasiStrictNE.PPADComplete (CakeProblem .binary true) ∧
    QuasiStrictNE.PPADComplete (CakeProblem .unary true) := by sorry

end ContiguousCake597.Approximate
