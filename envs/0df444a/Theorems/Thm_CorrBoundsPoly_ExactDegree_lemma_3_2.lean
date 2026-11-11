-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_3_2
-- name    : CorrBoundsPoly.ExactDegree.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:53.089197+00:00
-- url     : https://prove2.me/theorems/3f7860cf-9e0a-4a5e-938b-ef5075e7a95c
-- title:
--   Lemma 3.2 — $\sigma_{j,m}(x)=\binom{|x|}{j}\bmod2=\prod_{t:j_t=1}w_t$; functions of $|x|\bmod2^a$ have degree $\le2^a-1$
-- statement:
--   For $x\in\mathbb F_2^m$ write $|x|$ for its Hamming weight and $|x|=\sum_tw_t2^t$ for its binary expansion. For every $j\ge0$, with $j=\sum_tj_t2^t$,
--   $$\sigma_{j,m}(x)=\binom{|x|}{j}\bmod 2=\prod_{t:\,j_t=1}w_t .$$
--   In particular $\sigma_{2^a,m}(x)=w_a$, and every Boolean function of $|x|\bmod 2^a$ has algebraic degree at most $2^a-1$.
--
--   The lemma makes the dyadic elementary cores evaluable from one binary digit of the Hamming weight, and supplies the low-degree tests that attain the exact correlation (Corollary 3.9).
--
--   Differences from the source:
--   - encoding: $\binom{|x|}{j}\bmod2$ and the bits $w_t$ → the natural number cast into `ZMod 2`, and `if (hw x).testBit t then 1 else 0`; reason: $\mathbb F_2=\{0,1\}$
--   - encoding: $\prod_{t:j_t=1}$ → product over $t\le j$ with `j.testBit t`; reason: every nonzero binary digit of $j$ has index at most $j$
--   - encoding: "a Boolean function of $|x|\bmod2^a$" → $x\mapsto g(|x|\bmod 2^a)$ for an arbitrary $g:\mathbb N\to\mathbb F_2$; "algebraic degree at most $2^a-1$" → `HasDegLE … (2 ^ a - 1)`; reason: same class of functions; $2^a\ge1$, so no truncation
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 26 (PDF 28), Lemma 3.2

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 3.2** (Binary form of the elementary symmetric functions; Xin Li, *More on Correlation
Bounds for Polynomials*, p. 26, PDF 28). For `j ≥ 0` and `x ∈ F₂^m`:
(1) `σ_{j,m}(x) = C(|x|, j) mod 2`, and, writing `j = ∑_t j_t 2^t`, `|x| = ∑_t w_t 2^t`, this equals
`∏_{t : j_t = 1} w_t`; (2) in particular `σ_{2^a,m}(x) = w_a`; (3) every Boolean function of
`|x| mod 2^a` has algebraic degree at most `2^a − 1`. -/
theorem lemma_3_2 (m : ℕ) :
    (∀ (j : ℕ) (x : Fin m → ZMod 2),
      MvPolynomial.eval x (sigma j m) = (((hw x).choose j : ℕ) : ZMod 2) ∧
        (((hw x).choose j : ℕ) : ZMod 2) =
          ∏ t ∈ (Finset.range (j + 1)).filter (fun t => j.testBit t),
            (if (hw x).testBit t then (1 : ZMod 2) else 0)) ∧
    (∀ (a : ℕ) (x : Fin m → ZMod 2),
      MvPolynomial.eval x (sigma (2 ^ a) m) = if (hw x).testBit a then 1 else 0) ∧
    (∀ (a : ℕ) (g : ℕ → ZMod 2), HasDegLE (fun x : Fin m → ZMod 2 => g (hw x % 2 ^ a)) (2 ^ a - 1)) := by sorry

end CorrBoundsPoly.ExactDegree
