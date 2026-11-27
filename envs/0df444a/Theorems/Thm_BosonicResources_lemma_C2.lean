-- Prove2me | Theorems.Thm_BosonicResources_lemma_C2
-- name    : BosonicResources.lemma_C2
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T06:28:04.25143+00:00
-- url     : https://prove2.me/theorems/6880d440-48f7-5e74-8a83-0b57ac0983ad
-- title:
--   Lemma C.2: classical measurements on Gaussian states are simulated by samples from the Wigner distribution
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$), and $\mathcal N(\mu,\Sigma)$ is the Gaussian probability measure on $\mathbb R^{2n}$ with mean $\mu$ and covariance $\Sigma$, the Wigner distribution of $\rho(\mu,\Sigma)$. A POVM on $N$ copies is *classical* if all of its elements have non-negative Wigner functions: for every measurable set $B$ of outcomes, the POVM element $E(B)$ has a Wigner function $W_{E(B)}\ge 0$, that is, a bounded measurable function $W_{E(B)}\ge0$ on the $N$-copy phase space $(\mathbb R^{2n})^{N}$ with $\langle u\rvert E(B)\lvert v\rangle=(2\pi)^{nN}\int W_{E(B)}(r)\,W_{\lvert v\rangle\langle u\rvert}(r)\,dr$ for all Fock states $u,v$ of the $N$ copies (here $W_{\lvert v\rangle\langle u\rvert}$ is the Wigner function of the Fock matrix unit).
--
--   Let $P$ be a classical POVM on $N$ copies of an $n$-mode system, with outcomes in a standard Borel space $\mathcal O$ (for example a finite or countable set, $\mathbb R^{d}$, or any Polish space with its Borel sets). Then there is a Markov kernel $\kappa$ from $(\mathbb R^{2n})^{N}$ to $\mathcal O$ such that, for every $n$-mode Gaussian state $\rho(\mu,\Sigma)$ and every measurable set $B\subseteq\mathcal O$,
--
--   $$
--   \Pr\big[\text{the outcome of }P\text{ on }\rho(\mu,\Sigma)^{\otimes N}\text{ lies in }B\big]=\int_{(\mathbb R^{2n})^{N}}\kappa(r,B)\;\mathcal N(\mu,\Sigma)^{\otimes N}(dr).
--   $$
--
--   In words: the outcome distribution of $P$ on $N$ copies of the state is exactly the distribution obtained by drawing $N$ independent samples from $\mathcal N(\mu,\Sigma)$ and applying the classical post-processing $\kappa$, and $\kappa$ is the same for all $(\mu,\Sigma)$.
--
--   This standard fact about POVMs with non-negative Wigner functions (quoted from [ME12]) reduces learning Gaussian states with classical measurements to a classical statistical problem about samples of a Gaussian distribution; it is how the classical-measurement hypothesis enters the $\Omega(n^{3}/\varepsilon^{2})$ lower bound of Theorem 2.
--
--   **Formalization Note** The kernel is chosen before $(\mu,\Sigma)$, which is "post-processing independent of $(\mu,\Sigma)$". $\rho^{\otimes N}$ is the published `WildeQIT.Schumacher.tensorPow`; $\mathcal N(\mu,\Sigma)^{\otimes N}$ is the product measure. The conclusion is an equality of measures on $\mathcal O$, between the Born law of the POVM and the composition (`Measure.bind`) of the product Gaussian measure with $\kappa$; classicality is `IsClassical`, and $N$ and $n$ are arbitrary. The kernel is the conditional distribution $p(x\mid\alpha)=(2\pi)^{nN}W_{M_x}(\alpha)$ of the paper's proof: $\kappa(r,B)=(2\pi)^{nN}W_{P(B)}(r)$ for almost every $r$. The outcome space is assumed standard Borel (`StandardBorelSpace`): for a countable discrete space the numbers $(2\pi)^{nN}W_{P(\{x\})}(r)$ are a probability vector for almost every $r$ and define $\kappa$ directly, and in general this assumption is what guarantees that the conditional probabilities $(2\pi)^{nN}W_{P(B)}(r)$, each defined up to a null set, come from one Markov kernel.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. C.1, Lemma C.2; quoting [ME12] (Mari, Eisert, PRL 2012)

import Mathlib
import Definitions.Def_BosonicLearn_collectiveSuccess
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsClassical
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Lemma C.2 (Classical measurements on Gaussian states are simulated by Wigner samples).**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, Lemma C.2 (App. C.1), quoting [ME12] (Mari, Eisert, PRL 2012): "Given N i.i.d. copies of an unknown n-mode
Gaussian state ρ(µ,Σ) and a POVM {M_x}_x on the N × n-mode Hilbert space, such that each POVM element M_x has
non-negative Wigner function, then the measurement outcome probability distribution p(x|ρ^{⊗N}) = Tr(M_x ρ^{⊗N}) can
be exactly simulated by sampling N i.i.d. samples from the Gaussian distribution N(µ,Σ) followed by classical
post-processing independent of (µ,Σ)."

For every classical POVM `P` on `N` copies of an `n`-mode system, with outcomes in a standard Borel space `O`, there is a
Markov kernel `κ` from `(ℝ²ⁿ)^N` to `O` such that for every Gaussian state `ρ(µ, Σ)` the outcome law of `P` on
`ρ^{⊗N}` is the law obtained by drawing `N` independent samples from `N(µ, Σ)` and applying `κ`.

**Formalization Note.** The kernel is chosen before `(µ, Σ)`, which is "post-processing independent of (µ,Σ)".
`ρ^{⊗N}` is the published `WildeQIT.Schumacher.tensorPow`; `N(µ,Σ)^{⊗N}` is the product measure. Classicality
(`IsClassical`) is non-negativity of the Wigner function `w_B` of every element `P(B)`; the kernel is the conditional
distribution `p(x|α) = (2π)^{nN} W_{M_x}(α)` of the paper's proof, `κ(r, B) = (2π)^{nN} w_B(r)` for almost every `r`.
The outcome space is assumed standard Borel (finite and countable discrete sets, `ℝᵈ`, Polish spaces with their
Borel sets): for a countable discrete space the numbers `(2π)^{nN} w_{{x}}(r)` are a probability vector for almost
every `r` and define `κ` directly, and in general a standard Borel space is what guarantees that the conditional
probabilities `(2π)^{nN} w_B(r)`, each defined up to a null set, come from one Markov kernel. -/
theorem lemma_C2 {n N : ℕ} {O : Type} [MeasurableSpace O] [StandardBorelSpace O]
    (P : FockPOVM (Fin N → Occupation (Fin n)) O) (hP : IsClassical P) :
    ∃ κ : Kernel (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) O, IsMarkovKernel κ ∧
      ∀ (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
          (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
        IsGaussianState ρ μ S →
        P.law (WildeQIT.Schumacher.tensorPow N ρ.coefficients) =
          (Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ) S).bind κ := by sorry

end BosonicResources
