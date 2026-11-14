-- Prove2me | Theorems.Thm_BosonicLearn_priorMu_prob
-- name    : BosonicLearn.priorMu_prob
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:24:00.349218+00:00
-- url     : https://prove2.me/theorems/6dd8772e-23b0-43a0-b15d-2868db9fad3b
-- title:
--   The prior $\mu\propto e^{-\frac n4\|X\|_F^2}\mathbb 1(\|X\|_{\rm op}\le4)$ on $\mathrm{Herm}_0(n)$ is a probability measure supported on $G_{\rm supp}$
-- statement:
--   The prior of the lower-bound argument is well defined.
--
--   Let $\mu$ be the measure on the space $\mathrm{Herm}_0(n)$ of traceless Hermitian $n\times n$ matrices with density
--
--   $$
--   \mu(X)=Z_\mu^{-1}\exp\!\big(-\tfrac n4\|X\|_{\mathrm F}^2\big)\,\mathbb 1(\|X\|_{\mathrm{op}}\le4)
--   $$
--
--   with respect to Lebesgue measure, $Z_\mu$ being the total mass of the unnormalized density. Then $0<Z_\mu<\infty$, so $\mu$ is a probability measure, and $\mu$-almost every $X$ lies in $G_{\mathrm{supp}}=\{X:\|X\|_{\mathrm{op}}\le4\}$.
--
--   Why it holds. $G_{\mathrm{supp}}$ is compact with non-empty interior in $\mathrm{Herm}_0(n)$ and the density is continuous, positive and at most $1$ on it.
--
--   Role. Averaging the success probability of a learner over $X\sim\mu$ uses that $\mu$ has total mass $1$ and that almost every $X$ gives a state of the hard family (proof of Theorem 5).
--
--   **Formalization Note** `priorMu n` is `(m univ)⁻¹ • m` with `m` the restriction of `Measure.addHaar` on `Herm0 n` to `Gsupp n` with the Gaussian density; the statement is `IsProbabilityMeasure (priorMu n)` and `∀ᵐ X ∂(priorMu n), X ∈ Gsupp n`. It holds for every $n$, including $n\le1$ where $\mathrm{Herm}_0(n)=\{0\}$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, Eq. (32), p. 30 (the prior µ: GUE*(n) conditioned on G_supp)

import Mathlib
import Definitions.Def_BosonicLearn_priorMu

open MeasureTheory
open scoped ENNReal

namespace BosonicLearn

/-- **The prior `µ` is a probability measure supported on `G_supp`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, Eq. (32), p. 30: "Sample X ∼ GUE*(n) conditioned on X ∈ G_supp. … The density of X with respect to the
Lebesgue measure on Herm_0(n) is given by µ(X) = Z_µ^{−1} exp(−(n/4)‖X‖_F²) 𝟙(‖X‖_op ≤ 4)."

`priorMu n` is a probability measure on `Herm₀(n)`, and `X ∈ G_supp` for `µ`-almost every `X`.

**Formalization Note.** `priorMu n` is defined by normalizing the measure with density
`exp(−(n/4)‖X‖_F²)` on `G_supp` against a Haar measure; the statement says the normalizing constant `Z_µ` is
finite and positive (`G_supp` is compact with non-empty interior in `Herm₀(n)`), and that the measure is
concentrated on `G_supp`. -/
theorem priorMu_prob (n : ℕ) :
    IsProbabilityMeasure (priorMu n) ∧ ∀ᵐ X ∂(priorMu n), X ∈ Gsupp n := by sorry

end BosonicLearn
