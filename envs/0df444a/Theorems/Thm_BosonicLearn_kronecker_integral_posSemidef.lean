-- Prove2me | Theorems.Thm_BosonicLearn_kronecker_integral_posSemidef
-- name    : BosonicLearn.kronecker_integral_posSemidef
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:21:33.090195+00:00
-- url     : https://prove2.me/theorems/bb86644b-0a6e-4a05-b3cf-04998adb5364
-- title:
--   $\int A(dx)\otimes G(x)\succeq0$ for a positive semidefinite matrix measure $A$ and a positive semidefinite matrix function $G$
-- statement:
--   The integral of a positive semidefinite matrix-valued function against a positive semidefinite matrix-valued measure is positive semidefinite on the tensor product.
--
--   Let $\iota_1,\iota_2,K$ be finite sets and $\Omega$ a measurable space. For $u,v\in\iota_1$ and $k\in K$ let $\mu_{uvk}$ be finite measures on $\Omega$ and $c_{uvk}$ complex numbers such that the matrix
--
--   $$
--   A(B)=\Big(\sum_{k\in K}c_{uvk}\,\mu_{uvk}(B)\Big)_{u,v\in\iota_1}
--   $$
--
--   is positive semidefinite for every measurable $B\subseteq\Omega$. Let $G:\Omega\to\mathbb C^{\iota_2\times\iota_2}$ have measurable entries with $|G(x)_{ab}|\le1$ and $G(x)$ positive semidefinite for every $x$. Then the matrix $W$ on $\iota_1\times\iota_2$ with entries
--
--   $$
--   W_{(u,a),(v,b)}=\sum_{k\in K}c_{uvk}\int_\Omega G(x)_{ab}\,\mathrm d\mu_{uvk}(x)\;=\;\int_\Omega A(\mathrm dx)_{uv}\,G(x)_{ab}
--   $$
--
--   is positive semidefinite.
--
--   Role. If $M$ is a POVM on a first system with outcomes $x\in\Omega$ and $Q_x$ is a POVM on a second system chosen according to $x$, the joint effect is $E'(C)=\int M(\mathrm dx)\otimes Q_x(C_x)$. This lemma, applied to finite blocks $A(B)=M(B)|_{s_1}$ and $G(x)=Q_x(C_x)|_{s_2}$, shows that $E'(C)$ is positive on all finitely supported vectors of the two-system space, entangled ones included. Positivity on product vectors alone would not suffice. It is the main step of `BosonicLearn.fockPOVM_compose`.
--
--   **Formalization Note** Positive semidefinite is `Matrix.PosSemidef` over $\mathbb C$ with the partial order of `ComplexOrder`; the measures enter through `(μ u v k B).toReal`. For constant $G$ the statement reduces to `Matrix.PosSemidef.kronecker`. The statement is pure matrix analysis and measure theory and uses no definition of the mission.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, p. 30 (adaptive protocols: the t-th POVM depends on earlier outcomes); auxiliary lemma for the proof of Theorem 3, p. 67

import Mathlib

open MeasureTheory
open scoped ENNReal Matrix ComplexOrder

namespace BosonicLearn

/-- **Integrating a positive-semidefinite matrix function against a positive-semidefinite matrix measure.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, p. 30: "the t-th POVM can depend on the first t − 1 measurement outcomes x_{<t}"; the joint
effect of a measurement followed by an outcome-dependent measurement on a second system is
`∫ M(dx) ⊗ Q_x`.

Let `ι₁, ι₂, K` be finite sets and `Ω` a measurable space. Let `A(B) = (∑ₖ c_{uvk} μ_{uvk}(B))_{u,v ∈ ι₁}` be a
matrix-valued set function, where the `μ_{uvk}` are finite measures on `Ω` and the `c_{uvk}` complex numbers,
such that `A(B)` is positive semidefinite for every measurable `B`. Let `G : Ω → ℂ^{ι₂ × ι₂}` be measurable with
`G(x)` positive semidefinite and entries of modulus at most `1`. Then the matrix on `ι₁ × ι₂` with entries

`W_{(u,a),(v,b)} = ∑ₖ c_{uvk} ∫ G(x)_{ab} dμ_{uvk}(x)`  (`= ∫ A(dx)_{uv} G(x)_{ab}`)

is positive semidefinite.

**Formalization Note.** Positive semidefinite is `Matrix.PosSemidef` over `ℂ` (with the order of
`ComplexOrder`). When `G` is constant this is the positivity of the Kronecker product `A(Ω) ⊗ G`. -/
theorem kronecker_integral_posSemidef {Ω ι₁ ι₂ K : Type} [MeasurableSpace Ω] [Fintype ι₁] [Fintype ι₂]
    [Fintype K] (μ : ι₁ → ι₁ → K → Measure Ω) (hμ : ∀ u v k, IsFiniteMeasure (μ u v k))
    (coef : ι₁ → ι₁ → K → ℂ)
    (hA : ∀ B : Set Ω, MeasurableSet B →
      (Matrix.of fun u v => ∑ k, coef u v k * (((μ u v k B).toReal : ℝ) : ℂ)).PosSemidef)
    (G : Ω → Matrix ι₂ ι₂ ℂ) (hGm : ∀ a b, Measurable fun x => G x a b)
    (hGb : ∀ x a b, ‖G x a b‖ ≤ 1) (hG : ∀ x, (G x).PosSemidef) :
    (Matrix.of fun (p q : ι₁ × ι₂) =>
      ∑ k, coef p.1 q.1 k * ∫ x, G x p.2 q.2 ∂(μ p.1 q.1 k)).PosSemidef := by sorry

end BosonicLearn
