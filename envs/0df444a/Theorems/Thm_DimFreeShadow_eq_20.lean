-- Prove2me | Theorems.Thm_DimFreeShadow_eq_20
-- name    : DimFreeShadow.eq_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:59.419203+00:00
-- url     : https://prove2.me/theorems/0314da65-6c71-4cf1-a0e9-71707ca87124
-- title:
--   Eq. (20) — the recovered label measures $\sum_x W(a\mid x)D_{x,t}$
-- statement:
--   Let $\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble: $\mathcal X$ finite, $p_x>0$, $\sum_x p_x=1$, each $\rho_x$ a state on $\mathcal H$. Let $W:\mathcal X\to[k]$ be a stochastic map and $t\ge0$. Take the reference $\Omega_{JQ^t}=\sum_{x,a}p_xW(a\mid x)|a\rangle\langle a|\otimes\rho_x^{\otimes t}$, with $a$-block $C_a=\sum_xp_xW(a\mid x)\rho_x^{\otimes t}$; its $Q^t$-marginal is $B_t$. Then
--
--   $$
--   \int_{\mathbb R}\beta_0(u)B_t^{-(1+iu)/2}C_aB_t^{-(1-iu)/2}\,du+\Big(\sum_xp_xW(a\mid x)\Big)(I-P_t)=\sum_xW(a\mid x)D_{x,t},
--   $$
--
--   and this is the full-space effect of the recovered label: applying the completed recovery $\widehat R$ of Eq. (41) to an operator $X$ on $\mathcal H^{\otimes t}$, discarding the recovered $Q^t$ and reading the label $a$ gives
--
--   $$
--   \operatorname{Tr}\big[(\langle a|\otimes I)\widehat R(X)(|a\rangle\otimes I)\big]=\operatorname{Tr}\Big[\Big(\sum_xW(a\mid x)D_{x,t}\Big)X\Big].
--   $$
--
--   So every choice of $W$ gives a classical post-processing of the same effects $D_{x,t}$.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: the "full space classical effect for label a" of the completed recovery → the identity of traces against every operator X, as well as the operator identity (20); reason: an effect is determined by its traces against all operators
--   - encoding: 0 ≤ t < N → every t : ℕ, with N absent; reason: N is arbitrary and plays no other part in Eq. (20); the same instances
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §4.2, Eq. (20), p.18; App. B.2, p.36

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DimFreeShadow_recoveryEffect
import Definitions.Def_DimFreeShadow_labelRecovery

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)
open QAlgorithms.Papers.Independent.Dependency50.P21 (betaZero)

/-- **Eq. (20): the recovered label measures `Σ_x W(a|x) D_{x,t}`** (arXiv:2608.06345, sha256
a1a42249…, §4.2, Eq. (20), p.18, with App. B.2, p.36). Fix a finite ensemble `{(p_x, ρ_x)}`, a
stochastic map `W : X → [k]` and `t ≥ 0`. Apply the completed label recovery `R̂` (Eq. (41)) for
the reference `Ω_{JQ^t} = Σ_{x,a} p_x W(a|x) |a⟩⟨a| ⊗ ρ_x^{⊗t}`, whose `a`-block is
`C_a = Σ_x p_x W(a|x) ρ_x^{⊗t}` and whose `Q^t`-marginal is `B_t`, and read out the label `a`
after discarding the recovered `Q^t`. The resulting full-space classical effect for label `a`
is `Σ_x W(a|x) D_{x,t}`. The statement has three parts: the `Q^t`-marginal of the reference is
`B_t`; the effect identity (20) itself,
`∫ β₀(u) B_t^{−(1+iu)/2} C_a B_t^{−(1−iu)/2} du + (Σ_x p_x W(a|x)) (I − P_t) = Σ_x W(a|x) D_{x,t}`;
and, for every operator `X` on `H^{⊗t}`,
`Tr[(⟨a| ⊗ I) R̂(X) (|a⟩ ⊗ I)] = Tr[(Σ_x W(a|x) D_{x,t}) X]`.

**Formalization Note** The source's range `0 ≤ t < N` is every `t : ℕ`, since `N` is arbitrary
and plays no other part here. Labels `[k]` are `Fin k`; `W x a` is `W(a | x)`. `R̂` is
`labelCompletion` (the block recovery `R = ∫ β₀ R_u` on `P_t X P_t` plus the complement term
`Tr((I − P_t)X) Ω_{JQ^t}`), so the identity is a statement about the completed recovery
channel, not a rewriting of Eq. (5). The label readout is the trace of the `a`-block. -/
theorem eq_20 {X d : Type} [Fintype X] [DecidableEq X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (k : ℕ) (W : X → Fin k → ℝ)
    (hW0 : ∀ x a, 0 ≤ W x a) (hW1 : ∀ x, ∑ a, W x a = 1) (t : ℕ) :
    let C : Fin k → Matrix (Fin t → d) (Fin t → d) ℂ :=
      fun a => ∑ x, ((p x * W x a : ℝ) : ℂ) • tensorPow (ρ x) t
    let B : Matrix (Fin t → d) (Fin t → d) ℂ := ensembleState p ρ t
    ∑ a, C a = B ∧
    (∀ a : Fin k,
      Matrix.of (fun i j => ∫ u : ℝ, (betaZero u : ℂ) *
          (WildeQIT.Recover.supportPow B (-(1 + (u : ℂ) * Complex.I) / 2) * C a *
            WildeQIT.Recover.supportPow B (-(1 - (u : ℂ) * Complex.I) / 2)) i j) +
        ((∑ x, p x * W x a : ℝ) : ℂ) • (1 - WildeQIT.Recover.supportProj B) =
      ∑ x, (W x a : ℂ) • recoveryEffect p ρ t x) ∧
    ∀ (a : Fin k) (Y : Matrix (Fin t → d) (Fin t → d) ℂ),
      ∑ q, labelCompletion C Y (a, q) (a, q) =
        ((∑ x, (W x a : ℂ) • recoveryEffect p ρ t x) * Y).trace := by sorry

end DimFreeShadow
