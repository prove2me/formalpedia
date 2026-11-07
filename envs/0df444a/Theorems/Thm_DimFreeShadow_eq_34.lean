-- Prove2me | Theorems.Thm_DimFreeShadow_eq_34
-- name    : DimFreeShadow.eq_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:03.365211+00:00
-- url     : https://prove2.me/theorems/c0c04006-7531-4e22-9550-763d53246a83
-- title:
--   Eq. (34) — the threshold observable and its Hoeffding bounds
-- statement:
--   Let $E$ be an effect, $k\ge1$, $c\in\mathbb R$, and let $F$ be the threshold observable of Algorithm 3. Then $F$ is an effect on $\mathcal H^{\otimes k}$. For every state $\rho$, with $\theta=\operatorname{Tr}(E\rho)$ and $p=\operatorname{Tr}(\rho^{\otimes k}F)$,
--
--   $$
--   p=\Pr\Big[\frac1k\sum_{i=1}^kV_i\ge c\Big]=\sum_{v:\,k^{-1}\sum_iv_i\ge c}\ \prod_{i=1}^k\theta^{v_i}(1-\theta)^{1-v_i},\qquad V_i\overset{\text{i.i.d.}}{\sim}\mathrm{Bernoulli}(\theta).
--   $$
--
--   For every $\gamma>0$,
--
--   $$
--   \theta\le c-\gamma\implies p\le e^{-2k\gamma^2},\qquad\theta\ge c+\gamma\implies1-p\le e^{-2k\gamma^2}.
--   $$
--
--   Finally, with $k=\lceil C/\epsilon^2\rceil$ and $\gamma=\epsilon/4$, one has $e^{-2k\gamma^2}=e^{-k\epsilon^2/8}\le e^{-C/8}$, so this quantity is at most $1/8$ whenever $e^{-C/8}\le1/8$.
--
--   These bounds make one constant-accuracy call of Corollary 5.7 decide on which side of $c$ the value $\theta$ lies.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - generalization: θ_j, c_{j,s}, γ_s = ϵ_s/4 and k_s = ⌈C/ϵ_s²⌉ of stage s of Algorithm 3 → every effect E, every k ≥ 1, every real c and every γ > 0; the 1/8 step for every ϵ > 0 and every C with e^{−C/8} ≤ 1/8; reason: the source applies the same computation at these parameters, and the Lean statement specializes to them
--   - encoding: the Bernoulli probability Pr[k⁻¹ Σ V_i ≥ c] → the explicit finite sum over v ∈ {0,1}^k of the product law; reason: the definition of the law of k independent Bernoulli(θ) variables
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two Hermitian positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Algorithm 3, line 11, and the product formula, p.29; Eq. (34), p.30

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_thresholdObs

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Eq. (34): the threshold observable of Algorithm 3** (arXiv:2608.06345, sha256 a1a42249…,
Algorithm 3 line 11 and the product formula, p.29; Eq. (34), p.30). For an effect `E`, a block
length `k ≥ 1` and a threshold `c`, let
`F = Σ_{v∈{0,1}^k : k⁻¹Σ_i v_i ≥ c} ⊗_i (E if v_i = 1, I − E if v_i = 0)`. Then:
1. `F` is an effect on `H^{⊗k}`;
2. for every state `ρ`, with `θ = Tr(Eρ)`, `p := Tr(ρ^{⊗k} F) = Pr[k⁻¹ Σ_i V_i ≥ c]` for
   `V_1, …, V_k` i.i.d. Bernoulli(`θ`), i.e. `p = Σ_{v : k⁻¹Σv_i ≥ c} ∏_i θ^{v_i}(1 − θ)^{1−v_i}`;
3. for every `γ > 0`: `θ ≤ c − γ ⇒ p ≤ e^{−2kγ²}` and `θ ≥ c + γ ⇒ 1 − p ≤ e^{−2kγ²}` (34);
4. with `k = ⌈C/ϵ²⌉` and `γ = ϵ/4`, `e^{−2kγ²} = e^{−kϵ²/8} ≤ e^{−C/8} ≤ 1/8` whenever
   `e^{−C/8} ≤ 1/8`.

**Formalization Note** `{0,1}^k` is `Fin k → Bool`; the filter in clause 2 is the one in the
definition of `thresholdObs`. Traces through real parts. Clause 4 is the arithmetic step of
Eq. (34) for every `ϵ > 0` and every real `C`. -/
theorem eq_34 {d : Type} [Fintype d] [DecidableEq d] (E : Matrix d d ℂ)
    (hE : QAlgorithms.IsEffect E) (k : ℕ) (hk : 1 ≤ k) (c : ℝ) :
    QAlgorithms.IsEffect (thresholdObs E k c) ∧
    (∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ →
      (tensorPow ρ k * thresholdObs E k c).trace.re =
        ∑ v ∈ Finset.univ.filter
            (fun v : Fin k → Bool => c ≤ (k : ℝ)⁻¹ * ∑ i, (if v i then (1 : ℝ) else 0)),
          ∏ i, (if v i then (E * ρ).trace.re else 1 - (E * ρ).trace.re)) ∧
    (∀ ρ : Matrix d d ℂ, WildeQIT.IsDensityOperator ρ → ∀ γ : ℝ, 0 < γ →
      ((E * ρ).trace.re ≤ c - γ →
        (tensorPow ρ k * thresholdObs E k c).trace.re ≤ Real.exp (-2 * k * γ ^ 2)) ∧
      (c + γ ≤ (E * ρ).trace.re →
        1 - (tensorPow ρ k * thresholdObs E k c).trace.re ≤ Real.exp (-2 * k * γ ^ 2))) ∧
    (∀ C ϵ : ℝ, 0 < ϵ → Real.exp (-C / 8) ≤ 1 / 8 →
      Real.exp (-2 * (⌈C / ϵ ^ 2⌉₊ : ℝ) * (ϵ / 4) ^ 2) ≤ 1 / 8) := by sorry

end DimFreeShadow
