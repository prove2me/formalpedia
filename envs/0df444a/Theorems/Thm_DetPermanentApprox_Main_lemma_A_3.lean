-- Prove2me | Theorems.Thm_DetPermanentApprox_Main_lemma_A_3
-- name    : DetPermanentApprox.Main.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:31:25.111195+00:00
-- url     : https://prove2.me/theorems/c3f6af75-0508-4118-b6a1-d7f35cc63ce9
-- title:
--   Lemma A.3 — Costed dyadic exponential approximation
-- statement:
--   For a rational $x$, an integer $B\ge1$ with $|x|\le B$, and an integer $Q\ge0$, the explicit Taylor-and-rounding procedure returns a nonnegative dyadic $L$ with
--
--   $$L\le e^x\le L+2^{-Q}.$$
--
--   A finite Turing machine computes this rational output in polynomially many bit operations in $B,Q,\ell(x)$. The output is a multiple of $2^{-(Q+1)}$, as in the proof on p.26. The fixed encoding is binary for $x$ and unary for the accuracy and magnitude parameters. This supplies a charged elementary-function approximation, rather than a unit-cost exponential instruction.
--
--   Differences from the source:
--   - encoding: polynomial bit cost in B, Q and reduced rational length → Mathlib finite multitape Turing polynomial time with binary x and unary B,Q; reason: encoded length is linear in those quantities and the output uses a fixed reduced binary rational encoding
--   - encoding: an approximating dyadic number L → the explicit Taylor sum and dyadic grid of the proof on p.26; reason: this fixes the source algorithmic witness and its finer Q+1 grid without excluding an input
--   - generalization: the computation promise is stated for B at least one and absolute x at most B → the Turing machine computes the same finite formula also outside that promise, while approximation accuracy retains the promise; reason: the finite Taylor sum and rational rounding have polynomial bit cost on every encoded input
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), Lemma A.3, p. 26 (PDF p. 26); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Numerical
import Definitions.Def_DetPermanentApprox_Main_Analysis

namespace DetPermanentApprox.Main

theorem lemma_A_3 :
    Nonempty (Turing.TM2ComputableInPolyTime exponentialInputEncoding
      OnlineCRS.Combine.encRat exponentialOutput) ∧
    ∀ (x : ℚ) (B Q : ℕ), 1 ≤ B → |x| ≤ B →
      0 ≤ expApprox x B Q ∧
      (∃ a : ℕ, expApprox x B Q = a / (2 : ℚ) ^ (Q + 1)) ∧
      (expApprox x B Q : ℝ) ≤ Real.exp (x : ℝ) ∧
      Real.exp (x : ℝ) ≤ (expApprox x B Q : ℝ) + 1 / (2 : ℝ) ^ Q := by sorry

end DetPermanentApprox.Main
