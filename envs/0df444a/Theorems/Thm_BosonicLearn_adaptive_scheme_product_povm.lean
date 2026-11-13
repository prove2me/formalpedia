-- Prove2me | Theorems.Thm_BosonicLearn_adaptive_scheme_product_povm
-- name    : BosonicLearn.adaptive_scheme_product_povm
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-13T04:37:57.618363+00:00
-- url     : https://prove2.me/theorems/e28d150d-f0c0-48c1-a0a5-8bc0a8a33460
-- title:
--   An adaptive single-copy scheme is one POVM on $\mathcal H^{\otimes N}$ with the transcript as outcome
-- statement:
--   An adaptive sequence of single-copy measurements on $N$ copies is one measurement on the $N$-copy system.
--
--   Let $\mathcal H=\ell^2(\mathbb N^n)$ be the $n$-mode Fock space. An adaptive single-copy scheme on $N$ copies with outcomes in a measurable space $O$ assigns to every round $t\in\{1,\dots,N\}$ and every record $x_{<t}=(x_1,\dots,x_{t-1})$ of earlier outcomes a POVM $M^{(x_{<t})}$ on $\mathcal H$ with outcomes in $O$, measured on a fresh copy, such that the outcome law of round $t$ depends measurably on $x_{<t}$. For density operators $\tau_1,\dots,\tau_N$ on $\mathcal H$ let $T_{\tau_1,\dots,\tau_N}$ be the law on $O^N$ of the transcript when round $t$ measures $\tau_t$: the first outcome has law $B\mapsto\operatorname{Tr}(M(B)\tau_1)$, and given $x_{<t}$ the $t$-th outcome has law $B\mapsto\operatorname{Tr}\big(M^{(x_{<t})}(B)\,\tau_t\big)$.
--
--   Then there is a POVM $M$ on $\mathcal H^{\otimes N}$ with outcomes in $O^N$ such that for all density operators $\tau_1,\dots,\tau_N$ on $\mathcal H$ and every measurable $B\subseteq O^N$
--
--   $$
--   \operatorname{Tr}\!\big(M(B)\,\tau_1\otimes\cdots\otimes\tau_N\big)=T_{\tau_1,\dots,\tau_N}(B).
--   $$
--
--   For $\tau_1=\dots=\tau_N=\rho$ the right-hand side is the transcript law $T_\rho$ of the scheme on $N$ copies of $\rho$.
--
--   Role. This is the precise sense in which single-copy (non-entangled) schemes are a subclass of collective measurements on $\rho^{\otimes N}$. With `BosonicLearn.fockPOVM_postprocess` applied to the estimator it gives `BosonicLearn.adaptive_scheme_collective`.
--
--   **Formalization Note** The scheme is an `AdaptiveScheme n N O`; the right-hand side is `sequentialLaw` of the round kernels $x_{<t}\mapsto$ `S.round τ_t t`. The product state has entries $\prod_t\tau_t(u_t,v_t)$ on the index type $\{1,\dots,N\}\to\mathbb N^n$. $M$ is a `FockPOVM`, so its Born law is a probability measure on every density operator of the $N$-copy space, entangled ones included; the identity is asserted on product states. Non-identical factors are allowed because the statement composes round by round in that form.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. The proof of `BosonicLearn.traceDist_le_one` contains lemmas on nuclear expansions, their sums, and truncation to finite index sets.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30 ("A non-entangled adaptive learning protocol on N copies can be specified by a family of sequences of POVMs"); transcript likelihood Eq. (63), p. 35

import Mathlib
import Definitions.Def_BosonicLearn_AdaptiveScheme
import Definitions.Def_BosonicLearn_sequentialLaw
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **An adaptive single-copy scheme is one POVM on the `N` copies.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "A non-entangled adaptive learning protocol on N copies can be specified by a family of
sequences of POVMs {M_{x_1}}, …, {M^{(x_{<t})}_{x_t}}, … Here, the t-th POVM can depend on the first t − 1
measurement outcomes x_{<t}"; the transcript likelihood is the product over rounds, Eq. (63), p. 35.

For every adaptive single-copy scheme `S` on `N` copies of an `n`-mode system with outcomes in `O`, there is one POVM
`M` on the `N`-copy Fock space `ℓ²(ℕⁿ)^{⊗N}` with outcomes in `O^N` (the transcripts) such that, for all density
operators `τ₁, …, τ_N` on one copy, the Born law of `M` on the product state `τ₁ ⊗ ⋯ ⊗ τ_N` is the law of the
transcript obtained when round `t` measures `τ_t`: the first outcome has law `S.round τ₁`, and given the first
`t − 1` outcomes `x_{<t}` the `t`-th outcome has law `S.round τ_t` at `x_{<t}`.

**Formalization Note.** The product state has entries `∏ₜ τₜ(uₜ, vₜ)` on the index type `Fin N → ℕⁿ`; with all `τₜ`
equal to `ρ` it is `ρ^{⊗N}` and the right-hand side is `transcriptLaw S ρ`. `M` is a `FockPOVM`, so its Born law is
a probability measure on every density of the `N`-copy space, entangled ones included. Non-identical factors are
allowed because that is the form in which the statement composes round by round. -/
theorem adaptive_scheme_product_povm {n N : ℕ} {O : Type} [MeasurableSpace O] (S : AdaptiveScheme n N O) :
    ∃ M : FockPOVM (Fin N → Occupation (Fin n)) (Fin N → O),
      ∀ τ : Fin N → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ, (∀ t, IsDensity (τ t)) →
        M.law (Matrix.of fun u v => ∏ t, τ t (u t) (v t)) =
          sequentialLaw (fun t => S.round (τ t) t) N le_rfl := by sorry

end BosonicLearn
