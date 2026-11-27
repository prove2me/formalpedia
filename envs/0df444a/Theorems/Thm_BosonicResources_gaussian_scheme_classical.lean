-- Prove2me | Theorems.Thm_BosonicResources_gaussian_scheme_classical
-- name    : BosonicResources.gaussian_scheme_classical
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:54:42.388981+00:00
-- url     : https://prove2.me/theorems/90a7756e-967c-423d-8712-dff9f5b060fa
-- title:
--   Adaptive Gaussian measurement schemes are classical measurements
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). A *Gaussian (general-dyne) measurement with seed covariance $V$* is the POVM on one copy with outcomes $\xi\in\mathbb R^{2n}$ and elements $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, the displaced copies of a Gaussian seed state with covariance $V$. An *adaptive single-copy scheme* measures the $N$ copies one at a time, and the POVM applied to the $t$-th copy may depend on the outcomes of the first $t-1$ measurements.
--
--   A POVM on $N$ copies is *classical* if all of its elements have non-negative Wigner functions: for every measurable set $B$ of outcomes, the POVM element $E(B)$ has a Wigner function $W_{E(B)}\ge 0$, that is, a bounded measurable function $W_{E(B)}\ge0$ on the $N$-copy phase space $(\mathbb R^{2n})^{N}$ with $\langle u\rvert E(B)\lvert v\rangle=(2\pi)^{nN}\int W_{E(B)}(r)\,W_{\lvert v\rangle\langle u\rvert}(r)\,dr$ for all Fock states $u,v$ of the $N$ copies (here $W_{\lvert v\rangle\langle u\rvert}$ is the Wigner function of the Fock matrix unit).
--
--   Consider an adaptive single-copy scheme on $N$ copies of an $n$-mode system all of whose measurements are Gaussian measurements (the seed covariance may depend on the round and on the earlier outcomes), and a classical post-processing $\pi$, that is, a Markov kernel from transcripts $x\in(\mathbb R^{2n})^{N}$ to a measurable space $\mathcal O$. Then there exists a classical POVM $P$ on the $N$ copies, with outcomes in $\mathcal O$, such that for every state $\rho$ of the $n$-mode system and every measurable set $B\subseteq\mathcal O$
--
--   $$
--   \Pr\big[\text{the outcome of }P\text{ on }\rho^{\otimes N}\text{ lies in }B\big]=\int_{(\mathbb R^{2n})^{N}}\pi(x,B)\;T_\rho(dx),
--   $$
--
--   where $T_\rho$ is the joint distribution of the $N$ outcomes (the transcript) when the scheme is run on $N$ copies of $\rho$.
--
--   This makes precise, at the level of whole protocols, the paper's remark that Gaussian measurements are classical measurements. It is the link through which the lower bound for classical measurements (Theorem 2) applies to Gaussian measurement schemes such as the adaptive algorithm of [BMEM25].
--
--   **Formalization Note** This is the statement that lets lower bounds for classical POVMs (`theorem_2`) apply to adaptive Gaussian protocols; without the classicality clause it is the published `BosonicLearn.adaptive_scheme_collective`. The state $\rho$ ranges over all density operators, not only Gaussian ones. The scheme is a `BosonicLearn.AdaptiveScheme` with `IsGaussianScheme`; the conclusion is an equality of measures between the Born law of $P$ on $\rho^{\otimes N}$ and the transcript law composed with the kernel; classicality is `IsClassical`. The statement covers adaptive single-copy schemes; the ancilla-assisted and multi-copy Gaussian measurements mentioned in Theorem S3 are not part of it.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (Gaussian measurements as examples of classical measurements); Sec. 3.2 (remark after Theorem 2); App. C.1, Theorem S3 and the remark after it

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicResources_IsGaussianMeasurement
import Definitions.Def_BosonicResources_IsClassical
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Gaussian measurement schemes are classical measurements.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "The most well-known example of classical measurements are Gaussian measurements (or, general-dyne
measurements)"; after Theorem 2: "Recall that Gaussian measurements are classical measurements. Theorem 2 implies
that [BMEM25]'s adaptive learning algorithm … is nearly optimal among all Gaussian measurement schemes"; Theorem S3:
"general (possibly adaptive, ancilla-assisted, multi-copy) Gaussian measurements … The above theorem actually applies
for any (collective) POVM whose elements all have non-negative Wigner functions, including Gaussian measurements as a
special case."

For every adaptive single-copy scheme on `N` copies all of whose measurements are Gaussian measurements, and every
classical post-processing (a Markov kernel `post` from transcripts to a measurable space `O`), there is a classical
POVM `P` on the `N` copies with outcomes in `O` such that, for every state `ρ`, the outcome law of `P` on `ρ^{⊗N}` is
the law of the post-processed transcript of the scheme on `N` copies of `ρ`.

**Formalization Note.** This is the statement that lets lower bounds for classical POVMs (`theorem_2`) apply to
adaptive Gaussian protocols; without the classicality clause it is the published `BosonicLearn.adaptive_scheme_collective`. -/
theorem gaussian_scheme_classical {n N : ℕ} {O : Type} [MeasurableSpace O]
    (Sch : AdaptiveScheme n N (EuclideanSpace ℝ (Fin n ⊕ Fin n))) (hG : IsGaussianScheme Sch)
    (post : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) O) (hpost : IsMarkovKernel post) :
    ∃ P : FockPOVM (Fin N → Occupation (Fin n)) O, IsClassical P ∧
      ∀ ρ : State (Occupation (Fin n)),
        P.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients) =
          (transcriptLaw Sch ρ.coefficients).bind post := by sorry

end BosonicResources
