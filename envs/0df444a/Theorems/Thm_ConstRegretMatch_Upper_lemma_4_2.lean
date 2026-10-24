-- Prove2me | Theorems.Thm_ConstRegretMatch_Upper_lemma_4_2
-- name    : ConstRegretMatch.Upper.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:14.769637+00:00
-- url     : https://prove2.me/theorems/7c16d10c-e720-4322-8e7f-3be400bb77bd
-- title:
--   Lemma 4.2, p. 21 — drift condition ∫P(x,dy)g(y) − g(x) ≤ −f(x) + c implies ∫π f ≤ c for every stationary π
-- statement:
--   Let $X$ be a discrete-time Markov chain on a measurable space $\mathcal S$ with transition kernel $P$, and let $f,g:\mathcal S\to\mathbb R$ be measurable and nonnegative, with $g$ integrable under every $P(x,\cdot)$. Suppose that for a constant $c$,
--   $$\int_{\mathcal S}P(x,dy)\,g(y)-g(x)\le-f(x)+c\qquad\text{for all }x\in\mathcal S. \tag{5}$$
--   Then for every stationary distribution $\pi$ of $X$, $f$ is $\pi$-integrable and
--   $$\int_{\mathcal S}\pi(dx)\,f(x)\le c. \tag{6}$$
--
--   This is the Foster–Lyapunov bound of Glynn and Zeevi (2008, Corollary 4) that the paper uses to bound stationary expectations; it requires no integrability of $g$ under $\pi$.
--
--   **Formalization Note** The chain is represented by its Markov kernel $P$; a stationary distribution is a probability measure $\pi$ with $\pi P=\pi$ (`Kernel.Invariant`). Measurability of $f,g$ and the integrability of $g$ under each $P(x,\cdot)$ are added so that the integral in (5) is the genuine one; the conclusion asserts integrability of $f$ under $\pi$ so that the Bochner integral in (6) is not a default value.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 21, Lemma 4.2 (citing Glynn and Zeevi 2008, Corollary 4)

import Mathlib

namespace ConstRegretMatch.Upper

open MeasureTheory ProbabilityTheory

/-- Lemma 4.2, p. 21 (Glynn and Zeevi 2008, Corollary 4). Let `P` be the transition kernel of a
discrete-time Markov chain on a measurable space `S`, and let `f, g : S → ℝ` be measurable and
nonnegative, with `g` integrable under every `P(x, ·)`. If for some constant `c`
`∫ P(x, dy) g(y) - g(x) ≤ -f(x) + c` for all `x` (5), then every stationary distribution `π` of the
chain has `f` integrable and `∫ π(dx) f(x) ≤ c` (6). -/
theorem lemma_4_2 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : ∀ x, Integrable g (P x)) (c : ℝ)
    (hdrift : ∀ x, ∫ y, g y ∂(P x) - g x ≤ -f x + c)
    (π : Measure S) [IsProbabilityMeasure π] (hπ : P.Invariant π) :
    Integrable f π ∧ ∫ x, f x ∂π ≤ c := by sorry

end ConstRegretMatch.Upper
