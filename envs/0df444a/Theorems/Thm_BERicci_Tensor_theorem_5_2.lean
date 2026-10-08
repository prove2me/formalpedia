-- Prove2me | Theorems.Thm_BERicci_Tensor_theorem_5_2
-- name    : BERicci.Tensor.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:31.553191+00:00
-- url     : https://prove2.me/theorems/35065366-fc41-4736-bc34-cf3c74a5bf19
-- title:
--   Theorem 5.2, p. 61 — a product of Riemannian Energy measure spaces with BE(K,N_X), BE(K,N_Y) is a Riemannian Energy measure space with BE(K,N_X+N_Y)
-- statement:
--   Let $(X,\tau_X,\mathcal E^X,\mathfrak m_X)$ and $(Y,\tau_Y,\mathcal E^Y,\mathfrak m_Y)$ be Riemannian Energy measure spaces (Definition 3.16) on complete separable metric spaces whose distances are the intrinsic distances $\mathsf d_{\mathcal E^X}$, $\mathsf d_{\mathcal E^Y}$, satisfying the Bakry–Émery conditions $\mathrm{BE}(K,N_X)$ and $\mathrm{BE}(K,N_Y)$, and satisfying (MD.exp). Let $\mathcal E$ be the Cartesian Dirichlet form (5.2) on $Z=X\times Y$ with the product topology and $\mathfrak m=\mathfrak m_X\times\mathfrak m_Y$, and let $(\mathsf P_t)$ be its heat flow. Then
--
--   1. $(Z,\tau,\mathfrak m,\mathcal E)$ is a Riemannian Energy measure space, and its intrinsic distance $\mathsf d_{\mathcal E}$ coincides with the product distance
--   $$\mathsf d((x,y),(x',y'))=\sqrt{\mathsf d_X^2(x,x')+\mathsf d_Y^2(y,y')};$$
--   2. $(Z,\tau,\mathfrak m,\mathcal E)$ satisfies $\mathrm{BE}(K,N_X+N_Y)$.
--
--   This is the tensorization of the Bakry–Émery condition with the natural bound on the dimension of the product.
--
--   **Formalization Note** $\mathrm{BE}(K,N)$ is parametrized by $\nu=1/N\ge0$, so $\mathrm{BE}(K,N_X+N_Y)$ is $\mathrm{BE}$ with $\nu_Z=\nu_X\nu_Y/(\nu_X+\nu_Y)$, the value used in the proof; it is $0$ ($N=\infty$) as soon as one factor has $N=\infty$. $Z$ is `WithLp 2 (X × Y)`, whose metric is the product distance (5.1); clause 1's identification $\mathsf d_{\mathcal E}=\mathsf d$ is part of being an Energy measure space on that carrier. The same truncation profile $S$ of (3.27) is used for $X$, $Y$ and $Z$. **Added hypothesis**: (MD.exp) for both factors. The proof starts from Theorem 5.1, which needs $\mathrm{RCD}(K,\infty)$ factors; a Riemannian Energy measure space with $\mathrm{BE}(K,\infty)$ is $\mathrm{RCD}(K,\infty)$ by Theorem 4.17 only under (MD.exp), which Theorem 5.2 does not list (§5.1 opens with $\mathrm{RCD}(K,\infty)$ spaces, whose definition contains it). The factors are also assumed σ-finite, as Mathlib's product measure needs.
-- source:
--   arXiv:1209.5786v4, Theorem 5.2, p. 61; (5.1)–(5.2), p. 59; proof, pp. 61–62

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Tensor_Product
open MeasureTheory Filter Topology
open scoped ENNReal

namespace BERicci.Tensor

/-- **Theorem 5.2**, p. 61. Let `(X, τ_X, E_X, m_X)`, `(Y, τ_Y, E_Y, m_Y)` be Riemannian Energy
measure spaces satisfying `BE(K, N_X)` and `BE(K, N_Y)` (written with `ν_X = 1/N_X`,
`ν_Y = 1/N_Y`), and let `E` be the Cartesian form (5.2) on `Z = X × Y` with the product topology
and `m = m_X × m_Y`. Then `(Z, τ, m, E)` is a Riemannian Energy measure space whose intrinsic
distance `d_E` is the product distance (5.1) (the metric of `WithLp 2 (X × Y)`, through
`IsEnergyMeasureSpace.dist_eq`), and it satisfies `BE(K, N_X + N_Y)`, i.e. `BE` with
`ν_Z = ν_X ν_Y/(ν_X + ν_Y)`. Added and disclosed: (MD.exp) for both factors. -/
theorem theorem_5_2
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] [SecondCountableTopology Y]
    (mX : Measure X) (mY : Measure Y) [SigmaFinite mX] [SigmaFinite mY]
    (EX : (X → ℝ) → ℝ≥0∞) (EY : (Y → ℝ) → ℝ≥0∞)
    (S : ℝ → ℝ) (hS : BERicci.Gamma.IsTruncProfile S)
    (hX : BERicci.Gamma.IsRiemannianEMS mX EX S) (hY : BERicci.Gamma.IsRiemannianEMS mY EY S)
    (hexpX : BERicci.Gamma.MDexp mX) (hexpY : BERicci.Gamma.MDexp mY)
    (PX : ℝ → (X → ℝ) → X → ℝ) (hPX : BERicci.Gamma.IsHeatSemigroup mX EX PX)
    (PY : ℝ → (Y → ℝ) → Y → ℝ) (hPY : BERicci.Gamma.IsHeatSemigroup mY EY PY)
    (K νX νY : ℝ) (hBX : BERicci.Gamma.BE mX EX PX K νX) (hBY : BERicci.Gamma.BE mY EY PY K νY)
    (PZ : ℝ → (WithLp 2 (X × Y) → ℝ) → WithLp 2 (X × Y) → ℝ)
    (hPZ : BERicci.Gamma.IsHeatSemigroup (prodMeasure mX mY) (cartesianForm mX mY EX EY) PZ) :
    BERicci.Gamma.IsRiemannianEMS (prodMeasure mX mY) (cartesianForm mX mY EX EY) S ∧
      BERicci.Gamma.BE (prodMeasure mX mY) (cartesianForm mX mY EX EY) PZ K (νX * νY / (νX + νY)) := by sorry

end BERicci.Tensor
