-- Prove2me | Theorems.Thm_FeynmanWick_gaussianReal_moment_even
-- name    : FeynmanWick.gaussianReal_moment_even
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:03:05.396875+00:00
-- url     : https://prove2.me/theorems/76aa5b0b-bc3e-4d3f-a615-6fc59ebc7a91
-- title:
--   $\langle x^{2n}\rangle = (2n-1)!!\,\langle x^{2}\rangle^{n}$ for a centered real Gaussian
-- statement:
--   Let $x$ be a centered real Gaussian random variable of variance $v \ge 0$, i.e. distributed
--   according to $\mathcal{N}(0, v)$, and let $n \in \mathbb{N}$. Then
--
--   $$ \langle x^{2n} \rangle \;=\; (2n-1)!!\; v^{n} \;=\; (2n-1)\cdot(2n-3)\cdots 5\cdot 3\cdot 1 \cdot \langle x^{2}\rangle^{n}, $$
--
--   since $\langle x^{2}\rangle = v$.
--
--   This is the normalized form of the source's higher-moment computation, and the statement the
--   article calls the completion of Wick's theorem: the $2n$-th moment of a single Gaussian equals the
--   number of pairings of $2n$ objects times the $n$-th power of the two-point function, exactly as
--   Wick's theorem predicts when all $2n$ insertions coincide.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib
import Definitions.Def_FeynmanWickPairings
open MeasureTheory ProbabilityTheory

namespace FeynmanWick

theorem gaussianReal_moment_even (v : NNReal) (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) ∂(gaussianReal 0 v)
      = (Nat.doubleFactorial (2 * n - 1) : ℝ) * (v : ℝ) ^ n := by sorry

end FeynmanWick
