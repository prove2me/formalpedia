-- Prove2me | Theorems.Thm_BosonicLearn_fockPOVM_compose
-- name    : BosonicLearn.fockPOVM_compose
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T05:28:10.625906+00:00
-- url     : https://prove2.me/theorems/a8873a68-1669-4999-a119-7795dadbf2b7
-- title:
--   Measuring one system, then a second one with a POVM chosen from the first outcome, is a single POVM on both
-- statement:
--   Measuring a first system and then measuring a second system with a POVM chosen according to the first outcome is a single measurement on the joint system.
--
--   Let $M$ be a POVM on $\ell^2(J)$ with outcomes in a measurable space $\Omega$. For every $x\in\Omega$ let $Q_x$ be a POVM on $\ell^2(I')$ with outcomes in a measurable space $O$, depending measurably on $x$ in the following sense: for every density operator $\tau$ on $\ell^2(I')$ there is a Markov kernel $\kappa_\tau$ from $\Omega$ to $O$ with $\kappa_\tau(x,\cdot)$ equal to the outcome law of $Q_x$ on $\tau$.
--
--   Then there is a POVM $M'$ on $\ell^2(J\times I')=\ell^2(J)\otimes\ell^2(I')$ with outcomes in $\Omega\times O$ such that for all density operators $\rho$ on $\ell^2(J)$ and $\tau$ on $\ell^2(I')$ and every measurable $C\subseteq\Omega\times O$
--
--   $$
--   M'_{\rho\otimes\tau}(C)=\int_\Omega\kappa_\tau\big(x,\{o:(x,o)\in C\}\big)\,\mathrm dM_\rho(x),
--   $$
--
--   where $M_\rho$ and $M'_{\rho\otimes\tau}$ denote outcome laws. In terms of effects, $E'(A\times B)=\int_AE(\mathrm dx)\otimes G_x(B)$, with $E$ and $G_x$ the effects of $M$ and $Q_x$.
--
--   Role. This is one round of an adaptive protocol: the first system carries the copies already measured, with the transcript so far as outcome, and the second system is the next copy. Iterating it gives `BosonicLearn.adaptive_scheme_product_povm`.
--
--   **Formalization Note** The operator $\rho\otimes\tau$ has entries $\rho(u,v)\,\tau(a,b)$ at $((u,a),(v,b))$, and the right-hand side is the composition-product `(M.law ρ) ⊗ₘ (κ τ)`. The measurable dependence on $x$ is given as data: a kernel `κ τ` for every coefficient array `τ`, Markov, and equal to `(Q x).law τ` on densities; this is how `AdaptiveScheme` provides its round laws. $M'$ is a `FockPOVM`, so its effects are bounded between $0$ and $\mathbf 1$ on all finitely supported vectors of the joint system and its Born law is a probability measure on every density operator of the joint system, entangled ones included.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators), `BosonicLearn.effect_trace_pairing` (Born sums along nuclear expansions), `BosonicLearn.fockPOVM_form_measure` (effects are weakly $\sigma$-additive) and `BosonicLearn.fockPOVM_postprocess`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30 ("the t-th POVM can depend on the first t − 1 measurement outcomes x_{<t}"); §4, p. 19 ("the choice of POVM may depend on all previous classical outcomes")

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Sequential composition of a POVM with an outcome-dependent POVM on a second system.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "A non-entangled adaptive learning protocol on N copies can be specified by a family of
sequences of POVMs {M_{x_1}}, …, {M^{(x_{<t})}_{x_t}}, … Here, the t-th POVM can depend on the first t − 1
measurement outcomes x_{<t}"; also §4, p. 19 ("the choice of POVM may depend on all previous classical outcomes").

Let `M` be a POVM on `ℓ²(J)` with outcomes in `Ω`, and for every `x ∈ Ω` let `Q_x` be a POVM on `ℓ²(I')` with
outcomes in `O`, depending measurably on `x`: for every density operator `τ` on `ℓ²(I')` the map
`x ↦ (outcome law of Q_x on τ)` is a Markov kernel `κ_τ` from `Ω` to `O`. Then there is a POVM `M'` on
`ℓ²(J × I') = ℓ²(J) ⊗ ℓ²(I')` with outcomes in `Ω × O` such that for all density operators `ρ` on `ℓ²(J)` and `τ` on
`ℓ²(I')` the outcome law of `M'` on `ρ ⊗ τ` is the law of the pair `(x, o)` where `x` has the law of `M` on `ρ` and,
given `x`, `o` has the law of `Q_x` on `τ`.

**Formalization Note.** `ρ ⊗ τ` has entries `ρ(u, v) τ(a, b)` at `((u, a), (v, b))`. The joint law is the
composition-product `(M.law ρ) ⊗ₘ κ_τ`. The measurable dependence on `x` is given as data: kernels `κ τ` for
every coefficient array `τ`, required to be Markov and to agree with `(Q x).law τ` on densities; this is the form
in which `AdaptiveScheme` provides its round laws. `M'` is a `FockPOVM`, so its Born law is a probability measure
on every density of the two systems, entangled ones included. -/
theorem fockPOVM_compose {J I' Ω O : Type} [DecidableEq J] [DecidableEq I'] [MeasurableSpace Ω]
    [MeasurableSpace O] (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) :
    ∃ M' : FockPOVM (J × I') (Ω × O), ∀ (ρ : Matrix J J ℂ) (τ : Matrix I' I' ℂ),
      IsDensity ρ → IsDensity τ →
        M'.law (fun p q => ρ p.1 q.1 * τ p.2 q.2) = (M.law ρ) ⊗ₘ (κ τ) := by sorry

end BosonicLearn
