-- Prove2me | Theorems.Thm_BERicci_Tensor_lemma_5_3
-- name    : BERicci.Tensor.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:16.455966+00:00
-- url     : https://prove2.me/theorems/768d107a-0a90-4acb-b743-602c5289345c
-- title:
--   Lemma 5.3, p. 62 — the generator of the Cartesian form is Δ_X f^y + Δ_Y f^x
-- statement:
--   Let $(X,d_X,\mathfrak m_X)$ and $(Y,d_Y,\mathfrak m_Y)$ be the RCD$(K,\infty)$ spaces of §5.1. Let $\mathcal E^X=2\mathrm{Ch}_X$ and $\mathcal E^Y=2\mathrm{Ch}_Y$ be their Dirichlet forms, with generators $\Delta_X$, $\Delta_Y$, and let $\mathcal E$ be the Cartesian form (5.2) on $Z=X\times Y$ with $\mathfrak m=\mathfrak m_X\times\mathfrak m_Y$ and generator $\Delta_Z$. Assume that $f\in\mathbb V=D(\mathcal E)$ satisfies
--   $$(f^y,f^x)\in D(\Delta_X)\times D(\Delta_Y)\ \text{for }\mathfrak m\text{-a.e. }(x,y)\in Z,\qquad \Delta_Xf^y,\ \Delta_Yf^x\in L^2(Z,\mathfrak m).\tag{5.9}$$
--   Then $f\in D(\Delta_Z)$ and
--   $$\Delta_Zf(x,y)=\Delta_Xf^y(x)+\Delta_Yf^x(y)\qquad\text{for }\mathfrak m\text{-a.e. }(x,y)\in Z .$$
--
--   This identifies the Laplacian of the product, and is the last step of the proof of $\mathrm{BE}(K,N_X+N_Y)$ for the product.
--
--   **Formalization Note** The two Laplacians are given as functions $\Delta X,\Delta Y$ on $Z$ whose sections are the fibre Laplacians: for $\mathfrak m_Y$-a.e. $y$, $f^y\in D(\Delta_X)$ with $\Delta_Xf^y=(\Delta X)^y$, and for $\mathfrak m_X$-a.e. $x$, $f^x\in D(\Delta_Y)$ with $\Delta_Yf^x=(\Delta Y)^x$ — the fibrewise reading of "for $\mathfrak m$-a.e. $(x,y)$" that the proof uses. The RCD hypotheses and the identities $\mathcal E^X=2\mathrm{Ch}_X$, $\mathcal E^Y=2\mathrm{Ch}_Y$ restore §5.1's standing setting; σ-finiteness is assumed for the product measure.
-- source:
--   arXiv:1209.5786v4, Lemma 5.3, (5.9), p. 62

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Tensor_Product
open MeasureTheory Filter Topology
open scoped ENNReal

namespace BERicci.Tensor

/-- **Lemma 5.3**, p. 62. Let `E` be the Cartesian form (5.2) of the Cheeger forms of the
RCD factor spaces on
`Z = X × Y` with `m = m_X × m_Y`, and let `f ∈ 𝕍 = D(E)`. Suppose that `f^y ∈ D(Δ_X)` with
`Δ_X f^y = (ΔX)^y` for `m_Y`-a.e. `y`, that `f^x ∈ D(Δ_Y)` with `Δ_Y f^x = (ΔY)^x` for `m_X`-a.e. `x`,
and that `ΔX, ΔY ∈ L²(Z, m)` (5.9). Then `f ∈ D(Δ_Z)` and
`Δ_Z f(x, y) = Δ_X f^y(x) + Δ_Y f^x(y)` for m-a.e. `(x, y)`. -/
theorem lemma_5_3
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [CompleteSpace Y] [SecondCountableTopology Y]
    (mX : Measure X) (mY : Measure Y) [SigmaFinite mX] [SigmaFinite mY]
    (EX : (X → ℝ) → ℝ≥0∞) (EY : (Y → ℝ) → ℝ≥0∞)
    (K : ℝ) (hX : BERicci.Gamma.IsRCDInfty mX K) (hY : BERicci.Gamma.IsRCDInfty mY K)
    (hEXCh : EX = fun g => 2 * BERicci.Gamma.cheeger mX g)
    (hEYCh : EY = fun g => 2 * BERicci.Gamma.cheeger mY g)
    (hEX : BERicci.Gamma.IsDirichletForm mX EX) (hEY : BERicci.Gamma.IsDirichletForm mY EY)
    (f : WithLp 2 (X × Y) → ℝ) (hf : cartesianForm mX mY EX EY f < ⊤)
    (ΔX ΔY : WithLp 2 (X × Y) → ℝ)
    (hΔX : ∀ᵐ y ∂mY, BERicci.Gamma.IsGenerator mX EX (secAtY f y) (secAtY ΔX y))
    (hΔY : ∀ᵐ x ∂mX, BERicci.Gamma.IsGenerator mY EY (secAtX f x) (secAtX ΔY x))
    (hΔXL2 : MemLp ΔX 2 (prodMeasure mX mY)) (hΔYL2 : MemLp ΔY 2 (prodMeasure mX mY)) :
    BERicci.Gamma.IsGenerator (prodMeasure mX mY) (cartesianForm mX mY EX EY) f (ΔX + ΔY) := by sorry

end BERicci.Tensor
