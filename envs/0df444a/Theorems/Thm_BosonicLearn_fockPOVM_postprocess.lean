-- Prove2me | Theorems.Thm_BosonicLearn_fockPOVM_postprocess
-- name    : BosonicLearn.fockPOVM_postprocess
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T04:37:45.687455+00:00
-- url     : https://prove2.me/theorems/09eadbfc-4bfb-4d63-a429-4056e5b0cd66
-- title:
--   Post-processing a POVM by a Markov kernel is a POVM: $P'_\rho(B')=\int\kappa(x,B')\,dP_\rho(x)$
-- statement:
--   Applying a randomized classical map to the outcome of a measurement gives another measurement.
--
--   Let $I$ be an index set and let $P$ be a POVM on $\ell^2(I)$ with outcomes in a measurable space $\Omega$. It consists of effects $E(B)$ for measurable $B\subseteq\Omega$, with $0\le E(B)\le\mathbf 1$ and $E(\Omega)=\mathbf 1$, and of an outcome law $P_\rho$ for every density operator $\rho$, a probability measure on $\Omega$ given by the Born rule $P_\rho(B)=\operatorname{Tr}(E(B)\rho)$. Let $\kappa$ be a Markov kernel from $\Omega$ to a measurable space $\Omega'$: $\kappa(x,B')$ is the probability that the post-processed outcome lies in $B'$ when the measurement outcome is $x$.
--
--   Then there is a POVM $P'$ on $\ell^2(I)$ with outcomes in $\Omega'$ such that for every density operator $\rho$ and every measurable $B'\subseteq\Omega'$
--
--   $$
--   P'_\rho(B')=\int_\Omega\kappa(x,B')\,\mathrm dP_\rho(x).
--   $$
--
--   In terms of effects, $E'(B')=\int_\Omega\kappa(x,B')\,E(\mathrm dx)$.
--
--   Role. A measurement followed by a randomized estimator is thereby a single measurement whose outcome is the estimate. Together with `BosonicLearn.adaptive_scheme_product_povm` it shows that an adaptive single-copy learner is a special case of a collective one, which is how the proof of Theorem 3 applies the collective lower bound of Theorem 9 to single-copy schemes.
--
--   **Formalization Note** $P$ and $P'$ are `FockPOVM`s: the effects are coefficient arrays whose quadratic forms on finitely supported vectors lie between $0$ and $\|z\|^2$, and the Born rule $P'_\rho(B')=\operatorname{Re}\sum_i\sum_jE'(B')_{ij}\rho_{ji}$ is required on every density operator $\rho$, with trace-class meant in the nuclear-expansion sense of `IsDensity`. The law of the post-processed outcome is `Measure.bind`. The identity is stated for every coefficient array $\rho$; on arrays that are not densities both sides are unconstrained data, so the content is the statement on densities. The source uses this fact without stating it.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. The proof of `BosonicLearn.traceDist_le_one` contains lemmas on nuclear expansions, their sums, and truncation to finite index sets.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Eq. (105), p. 40 ("the state estimator ρ̂(x) that allows internal randomness"); used in the proof of Theorem 3, p. 67

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Classical post-processing of a POVM is a POVM.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Eq. (105), p. 40 ("the state estimator ρ̂(x) that allows internal randomness"); used in the proof of
Theorem 3, p. 67, where a single-copy scheme followed by its estimator is treated as one measurement.

Let `P` be a POVM on `ℓ²(I)` with outcomes in a measurable space `Ω`, and let `κ` be a Markov kernel from `Ω` to a
measurable space `Ω'` (a randomized map applied to the outcome). There is a POVM `P'` on `ℓ²(I)` with outcomes in
`Ω'` whose outcome law on every state is the law of the post-processed outcome:
`P'.law ρ = ∫ κ(x, ·) d(P.law ρ)(x)`.

**Formalization Note.** `P'` is a `FockPOVM`, so its effects are bounded between `0` and `1`, are normalized, and
satisfy the Born rule `P'.law ρ B = Re Tr(E'(B) ρ)` on every density operator `ρ`. The law of the post-processed
outcome is `Measure.bind`. The identity is stated for every coefficient array `ρ`; on arrays that are not densities
both sides are unconstrained data, so the content is the statement on densities. The source uses this without
stating it. -/
theorem fockPOVM_postprocess {I Ω Ω' : Type} [DecidableEq I] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : FockPOVM I Ω) (κ : Kernel Ω Ω') (hκ : IsMarkovKernel κ) :
    ∃ P' : FockPOVM I Ω', ∀ ρ : Matrix I I ℂ, P'.law ρ = (P.law ρ).bind κ := by sorry

end BosonicLearn
