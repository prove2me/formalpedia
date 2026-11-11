-- Prove2me | Theorems.Thm_AgnHalfMem_theorem_3_1
-- name    : AgnHalfMem.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:22.34491+00:00
-- url     : https://prove2.me/theorems/4d949c79-a013-4957-9e4c-1082437c33a4
-- title:
--   Theorem 3.1 (corrected: exponent $r'=\min(r,k,\ell)$) — closeness to an extractor implies agnostic hardness
-- statement:
--   There are constants $a>0$ and $K_0$ such that the following holds. Let $H$ be a finite nonempty index set of hypotheses $h:X\to\{-1,1\}$ (measurable), let $\mu$ be a probability measure on $X$, let $0\le\delta<1$, and let $M':X\times H\to[-1,1]$ be measurable in $x$ with
--   $$
--   \mathbb E_{x\sim\mu}\big|M'(x,h)-h(x)\big|\le\delta\qquad\text{for every } h\in H .
--   $$
--   Suppose $M'$ is a $(k,\ell)$-$L_2$-extractor with error $2^{-r}$ for $\mu$, and put $r'=\min(r,k,\ell)\ge K_0$. Then for every class $\mathcal G$ containing all $h\in H$, no randomized streaming algorithm with at most $2^{ak\ell}$ memory states (that is, $ak\ell$ bits) and at most $2^{ar'}$ samples agnostically learns $\mathcal G$ under marginal $\mu$, with probability $0.9$, to excess error
--   $$
--   \frac12-\frac\delta2-2^{-ar'} .
--   $$
--
--   This is the paper's general reduction from agnostic learning to weak learning of a nearby extractor matrix (via Theorem 2.2).
--
--   **The printed statement is corrected.** As printed, the theorem asserts the excess-error threshold $\tfrac12-\tfrac\delta2-2^{-\Omega(r)}$ and the sample bound $2^{\Omega(r)}$. This is false when $k\ll r,\ell$. Take $H=\{0,1\}^n$, $X=([n]\times\{0,1\})\sqcup\{0,1\}^n$, $k=\lceil\sqrt n\rceil$, $\mu=p\cdot\mathrm{Unif}([n]\times\{0,1\})+(1-p)\mathrm{Unif}(\{0,1\}^n)$ with $p=2^{-k}$, and $M=M'$ the $\pm1$ matrix with $M((j,\beta),h)=(-1)^{h_j+\beta}$ and $M(x,h)=(-1)^{\langle x,h\rangle}$. Then $\delta=0$ and $M'$ is a $(k-1,\Theta(n))$-extractor with error $2^{-\Theta(n)}$. A learner with $O(n)$ bits that reads about $n\log n\cdot2^{k}$ samples and estimates each coordinate from the "pair" rows outputs $\hat h$ with $\mathrm{err}(\hat h)\le\mathrm{OPT}+\tfrac12-p/4$ with probability $0.9$ for every $D$ with marginal $\mu$; this beats $\tfrac12-2^{-\Omega(r)}$ with $o(k\ell)$ memory and $2^{o(r)}$ samples. The proof's own conclusion (p.8) uses $r'=\min(r,k,\ell)$, which is the statement formalized here.
--
--   Differences from the source:
--   - correction: excess error 1/2 − δ/2 − 2^{−Ω(r)} and 2^{Ω(r)} samples → 1/2 − δ/2 − 2^{−a·r′} and T ≤ 2^{a·r′} with r′ = min(r, k, ℓ); reason: the printed form is false: for H = {0,1}ⁿ, k = ⌈√n⌉, a pair-row/parity-row matrix with δ = 0 is a (k−1, Θ(n))-extractor with error 2^{−Θ(n)}, yet an O(n)-bit learner with 2^{√n+O(log n)} samples reaches excess error 1/2 − 2^{−k−2}; the proof concludes with r′ = min(r, k, ℓ)
--   - encoding: Ω(kℓ) bits, 2^{Ω(·)}, "with high probability" → card S ≤ 2^{a·k·ℓ}, one constant a, success probability 0.9; reason: Ω means some positive constant; high probability is the 0.9 of §2
--   - reading: no size condition in the statement; Theorem 2.2, which the proof applies, assumes "sufficiently large k′, ℓ′ and r′" → K₀ ≤ min(r, k, ℓ); reason: the theorem inherits the asymptotic assumption of Theorem 2.2
--   - generalization: "any streaming algorithm" (deterministic branching programs WLOG, App. B) → every jointly measurable seeded family of branching programs on any seed space; reason: deterministic algorithms are the case of a one-point seed space
--   - encoding: H a finite set of hypotheses, M(x, h) = h(x), "or any hypothesis class containing H" → finite nonempty index type H with measurable hyp : H → X → Bool, M(x,h) = sgn(hyp h x), every G ⊇ range hyp; M′ measurable in x; reason: Lean conventions; expectations presuppose measurability
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Theorem 3.1, p.8 (proof p.8)

import Mathlib
import Definitions.Def_AgnHalfMem_sgn
import Definitions.Def_AgnHalfMem_IsL2Extractor
import Definitions.Def_AgnHalfMem_AgnLearnsUnder

open MeasureTheory

universe u v w w'

namespace AgnHalfMem

/-- **Theorem 3.1 (corrected: exponent `r′ = min(r, k, ℓ)`).** S. Garg, T. Jadhav,
*Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript,
PDF sha256 386bc9b3…43f84d5), Theorem 3.1, p.8: "Let H be a finite set and 0 ≤ δ < 1. Let
M : X × H → {−1, 1} be the corresponding learning matrix with M(x, h) = h(x), ∀x ∈ X, h ∈ H. If
there exists a probability measure µ over X and a matrix M′ : X × H → [−1, 1] such that for all
columns f indexed by hypothesis in H, E_{x∼µ}|M′(x, f) − M(x, f)| ≤ δ, and M′ is a
(k, ℓ)-L2-extractor with error 2^{−r}, w.r.t. µ, then any streaming algorithm that agnostically
learns the class H (or any hypothesis class containing H) under marginal µ, with high probability,
up to (1/2 − δ/2 − 2^{−Ω(r)}) excess error, requires Ω(kℓ) bits of memory or 2^{Ω(r)} samples."
The proof (p.8) concludes with "2^{Ω(r′)} samples (where r′ = min(r, k, ℓ))".

There are constants `a > 0` and `K₀` such that, with `r′ = min(r, k, ℓ) ≥ K₀`, no randomized
streaming algorithm with at most `2^{a k ℓ}` states and at most `2^{a r′}` samples agnostically
learns any class `G ⊇ H` under `μ` to excess error `1/2 − δ/2 − 2^{−a r′}`.

**Formalization Note.** The printed exponent `2^{Ω(r)}` is false (a counterexample with
`k = Θ(√n) ≪ r, ℓ = Θ(n)` is recorded in the item's description); the statement uses the proof's
own `r′ = min(r, k, ℓ)` in both places. "With high probability" is the `0.9` of §2. `H` is a finite
index type of hypotheses `hyp h : X → {±1}` (`M(x, h) = sgn(hyp h x)`); "sufficiently large" is
`K₀`. Hypotheses and `M′` are measurable. -/
theorem theorem_3_1 :
    ∃ a K₀ : ℝ, 0 < a ∧ 0 < K₀ ∧
      ∀ (H : Type u) [Fintype H] [Nonempty H] (X : Type v) [MeasurableSpace X]
        (μ : Measure X), IsProbabilityMeasure μ →
      ∀ (hyp : H → X → Bool), (∀ h, Measurable (hyp h)) →
      ∀ (M' : X → H → ℝ), (∀ h, Measurable fun x => M' x h) →
        (∀ x h, M' x h ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ δ : ℝ, 0 ≤ δ → δ < 1 → (∀ h, ∫ x, |M' x h - sgn (hyp h x)| ∂μ ≤ δ) →
      ∀ k l r : ℝ, IsL2Extractor μ M' k l r → K₀ ≤ min r (min k l) →
      ∀ G : Set (X → Bool), Set.range hyp ⊆ G →
      ∀ (Ω : Type w) (S : Type w') [MeasurableSpace Ω] [Fintype S] (T : ℕ)
        (A : StreamAlg Ω S X T) (P : Measure Ω), IsProbabilityMeasure P → IsMeasurableAlg A →
        (Fintype.card S : ℝ) ≤ (2 : ℝ) ^ (a * k * l) →
        (T : ℝ) ≤ (2 : ℝ) ^ (a * min r (min k l)) →
        ¬ AgnLearnsUnder μ G (1 / 2 - δ / 2 - (2 : ℝ) ^ (-(a * min r (min k l)))) A P := by sorry

end AgnHalfMem
