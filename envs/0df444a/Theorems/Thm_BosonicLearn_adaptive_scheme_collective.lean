-- Prove2me | Theorems.Thm_BosonicLearn_adaptive_scheme_collective
-- name    : BosonicLearn.adaptive_scheme_collective
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T02:49:12.945615+00:00
-- url     : https://prove2.me/theorems/339b3367-24ca-46a7-ba89-7d51c5f5c11d
-- title:
--   Adaptive single-copy schemes with randomized post-processing are collective POVMs on $\rho^{\otimes N}$
-- statement:
--   Every adaptive single-copy learning scheme, followed by any randomized classical post-processing, is realized by one collective measurement on all the copies.
--
--   Let $\mathcal H=\ell^2(\mathbb N^n)$ be the $n$-mode Fock space and let $\mathcal D(\mathcal H)$ be the set of density operators on $\mathcal H$, with the Borel $\sigma$-algebra of the trace-norm topology. An **adaptive single-copy scheme** on $N$ copies with outcomes in a measurable space $O$ assigns to every round $t\in\{1,\dots,N\}$ and every record $x_{<t}=(x_1,\dots,x_{t-1})$ of earlier outcomes a POVM $M^{(x_{<t})}$ on $\mathcal H$ with outcomes in $O$. The POVM is measured on a fresh copy, no quantum system is kept between rounds, and the outcome law of round $t$ depends measurably on $x_{<t}$. For a state $\rho\in\mathcal D(\mathcal H)$, let $T_\rho$ be the law of the transcript $x=(x_1,\dots,x_N)\in O^N$ when every round measures a fresh copy of $\rho$. A randomized **estimator** is a Markov kernel $\hat\rho$ from $O^N$ to $\mathcal D(\mathcal H)$; $\hat\rho(x,B)$ is the probability that the estimate lies in $B$ given the transcript $x$.
--
--   For every $n$ and $N$, every measurable space $O$, every adaptive single-copy scheme and every estimator $\hat\rho$, there is a POVM $E$ on the $N$-copy space $\mathcal H^{\otimes N}$, with outcomes in $\mathcal D(\mathcal H)$, such that for every state $\rho\in\mathcal D(\mathcal H)$ and every measurable $B\subseteq\mathcal D(\mathcal H)$
--
--   $$
--   \operatorname{Tr}\!\big(E(B)\,\rho^{\otimes N}\big)=\int_{O^N}\hat\rho(x,B)\,\mathrm dT_\rho(x).
--   $$
--
--   In words, the Born law of $E$ on $\rho^{\otimes N}$ is the law of the estimate that the scheme and its estimator produce from $N$ copies of $\rho$.
--
--   Role. Single-copy schemes are thereby a special case of collective (entangled) schemes, so a lower bound on the number of copies proved for collective measurements also holds for adaptive single-copy schemes. The proof of Theorem 3 uses this for $\nu>1$, where the collective lower bound of Theorem 9 is applied to single-copy learners.
--
--   **Formalization Note** The scheme is an `AdaptiveScheme n N O`, its transcript law is `transcriptLaw`, and the estimator is a Markov kernel into `State`. The POVM $E$ is a `FockPOVM` on the basis $\{1,\dots,N\}\to\mathbb N^n$ of $\mathcal H^{\otimes N}$; by definition its Born law is a probability measure on every density operator of the $N$-copy space, entangled ones included. The conclusion is the equality of measures `E.law (ρ^{⊗N}) = (transcriptLaw S ρ).bind est`, where $\rho^{\otimes N}$ has the entries $\prod_t\rho_{u_tv_t}$ (`WildeQIT.Schumacher.tensorPow`). The paper uses this inclusion of measurement classes without stating it as a separate result.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, proof of Theorem 3, p. 67 ("When ν > 1, Theorem 9 gives Ω(n²/ε²), even for arbitrary collective measurements"); single-copy measurement model §4, p. 19 and §5.1, p. 30

import Mathlib
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_WildeQIT_Schumacher_tensorPow
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Adaptive single-copy schemes are collective schemes.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, proof of Theorem 3, p. 67: "When ν > 1, Theorem 9 gives Ω(n²/ε²), even for arbitrary collective
measurements"; single-copy model, §4, p. 19 ("the choice of POVM may depend on all previous classical outcomes. No
quantum system is retained from one round to the next") and §5.1, p. 30 ("the t-th POVM can depend on the first
t − 1 measurement outcomes x_{<t}").

For every adaptive single-copy scheme `S` on `N` copies of an `n`-mode system, with outcomes in any measurable space
`O`, and every randomized estimator `est` (a Markov kernel from transcripts to density operators), there is one POVM
`E` on the `N`-copy Fock space `ℓ²(ℕⁿ)^{⊗N}`, with outcomes in the state space, whose Born law on every product state
`ρ^{⊗N}` is the law of the estimate `ρ̂` produced by running `S` on `N` fresh copies of `ρ` and then applying `est`:
`E.law(ρ^{⊗N}) = ∫ est(x, ·) dT_ρ(x)`, with `T_ρ` the transcript law.

**Formalization Note.** The law of the estimate is `Measure.bind` of the transcript law with the estimator kernel.
`E` is a `FockPOVM`, so its Born law is a probability measure on every density of the `N`-copy space, entangled ones
included; the identity is asserted on product states `ρ^{⊗N}` (`WildeQIT.Schumacher.tensorPow`). The paper uses this
inclusion of measurement classes without stating it. -/
theorem adaptive_scheme_collective {n N : ℕ} {O : Type} [MeasurableSpace O]
    (S : AdaptiveScheme n N O) (est : Kernel (Fin N → O) (State (Occupation (Fin n))))
    (hest : IsMarkovKernel est) :
    ∃ E : FockPOVM (Fin N → Occupation (Fin n)) (State (Occupation (Fin n))),
      ∀ ρ : State (Occupation (Fin n)),
        E.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients) =
          (transcriptLaw S ρ.coefficients).bind est := by sorry

end BosonicLearn
