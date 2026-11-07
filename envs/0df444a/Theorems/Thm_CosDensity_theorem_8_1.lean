-- Prove2me | Theorems.Thm_CosDensity_theorem_8_1
-- name    : CosDensity.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:41.959248+00:00
-- url     : https://prove2.me/theorems/2bb70183-e700-4481-a4a4-5da3ef870d47
-- title:
--   Theorem 8.1 — every one-pass $(1+\epsilon_p)$-approximation of $M_p$ under nonnegative cosine needs $\Omega_p(d^{\rho_p})$ bits
-- statement:
--   For every integer $p>2$, the exponent $\rho_p=\dfrac{p^2(p-1)}{2(p^2-2)}$ satisfies $\dfrac{p-1}2<\rho_p<\dfrac p2$, and there are constants $\epsilon_p>0$, $c>0$, $K$ and $d_0$, depending only on $p$, such that the following holds for every dimension $d\ge d_0$.
--
--   Let $A$ be a randomized one-pass streaming algorithm on vectors of $\mathbb R^d$ with a finite set $S$ of memory configurations. Suppose that, for every stream $P$ of unit vectors of $\mathbb R^d$ with pairwise nonnegative inner products, of length at most $d^K$, whose coordinates are rationals $a/b$ with $|a|,b\le d^K$, the output of $A$ is a $(1+\epsilon_p)$-approximation of $M_p(P)$ with probability at least $2/3$. Then
--
--   $$c\,d^{\rho_p}\le\log_2|S| .$$
--
--   That is, approximating the $p$-th cosine density moment under nonnegative cosine needs $\Omega_p(d^{\rho_p})$ bits, even for streams of polynomial length with $O_p(\log d)$-bit coordinates. Since $\rho_p>(p-1)/2$, the bound is superlinear in $d$ for every $p>2$.
--
--   Differences from the source:
--   - reading: a one-pass streaming algorithm whose memory is measured in bits → a finite configuration set S, memory log₂|S|; a persistent random seed not charged as memory; initial state, transitions and output may depend on the stream length and the position; real output; reason: the strongest class the proof supports (all hard streams share one length and one prefix length; the seed is the protocol's public coin), so the lower bound covers every narrower model
--   - reading: 1/3-error → for every stream of the class, some measurable event of probability ≥ 2/3 lies inside the success set; reason: this is weaker than requiring a measurable success set, so the theorem covers more algorithms, and it keeps the averaging step valid
--   - reading: Ω_p(d^{ρ_p}) for all sufficiently large d; length polynomial in d; O_p(log d) bits per coordinate → ∃ ε_p, c > 0, K, d₀ depending on p only, ∀ d ≥ d₀; correctness required only on the class of streams of length ≤ d^K with coordinates a/b, |a|, b ≤ d^K; reason: the 'even when' clause at full strength: the algorithm need only be correct on that class
--   - encoding: streams P = (x_1, …, x_n) of nonzero vectors, M_p over i ∈ [n] → nonempty Lean lists of unit vectors, M_p summed over positions with normalization u = x/‖x‖; reason: on unit streams normalization is the identity; repeated vectors count with multiplicity as in the paper
--   - encoding: every algorithm (seed space and memory configurations of any kind) → seed space Ω and configuration type S in Lean's base universe Type; reason: Lean universe convention; every finite configuration set and every seed space the proof uses (Fin k, Fin N → Bool, measure spaces of ordinary mathematics) lives in Type
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8, Theorem 8.1, pp.28–29 (pdf_page 29–30)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace CosDensity

/-- **Theorem 8.1** (space lower bound for `M_p` under nonnegative cosine). Q. Zhang, *Frequency
Moments Beyond Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version,
sha256 f4d4df22…), §8, Theorem 8.1, pp.28–29 (pdf_page 29–30).

For every fixed integer `p > 2` there is `ϵ_p > 0` such that, for all sufficiently large `d`, every
one-pass 1/3-error streaming algorithm that gives a `(1 + ϵ_p)`-approximation to `M_p(P)` for every
stream `P` of unit vectors in `ℝ^d` with pairwise nonnegative cosine similarities uses
`Ω_p(d^{ρ_p})` bits of space, `ρ_p = p²(p−1)/(2(p²−2)) ∈ ((p−1)/2, p/2)`; the bound holds even
when the streams have length polynomial in `d` and coordinates with `O_p(log d)` bits.

**Formalization Note.**
* Quantifiers: for every `p > 2` there are `ϵ_p > 0`, `c > 0`, `K` and `d₀`, depending on `p`
  only; then for every `d ≥ d₀` and every algorithm. `Ω_p(d^{ρ_p})` is `c d^{ρ_p} ≤ log₂ |S|`.
* "Length polynomial in `d`" and "`O_p(log d)` bits" are the class `InClass d K`: length at most
  `d^K` and coordinates `a/b` with `|a|, b ≤ d^K`. The algorithm only has to be correct on that
  class, which is the "even when" clause.
* The algorithm model is `StreamAlg` (a persistent public seed; transitions that may use the
  stream length and the position; real output); "1/3-error" is `SucceedsWP μ … (2/3)`.
* `ρ_p ∈ ((p−1)/2, p/2)` is the first conjunct. -/
theorem theorem_8_1 :
    ∀ p : ℕ, 2 < p →
      (((p : ℝ) - 1) / 2 < rho p ∧ rho p < (p : ℝ) / 2) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ K d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∀ (Ω S : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype S]
          (A : StreamAlg (EuclideanSpace ℝ (Fin d)) Ω S),
          (∀ P : List (EuclideanSpace ℝ (Fin d)), InClass d K P →
            SucceedsWP μ (fun ω => IsApprox ε (moment p P) (A.estimate ω P)) (2 / 3)) →
          c * (d : ℝ) ^ rho p ≤ memoryBits S := by sorry

end CosDensity
