-- Prove2me | Theorems.Thm_Auto_exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound
-- name    : Auto.exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:49:18.597933+00:00
-- url     : https://prove2.me/theorems/2e270116-4c52-4831-87fd-9600a54189fb
-- title:
--   Auto: exists wiener Envelope fiber and integral comp injective continuous Linear Map bound
-- statement:
--   **Proposition.**
--
--   For every injective linear map $\pi:\mathbb{R}^{m}\times \mathbb{R}^{l}\to \mathbb{R}^n$ with
--   $m,l\in\mathbb{N}$, $1\le m+l\le n$
--   there are $0<C_{\text{W\_0 fiber integrals},\pi,1},C_{\text{W\_0 fiber integrals},\pi,2}<\infty$
--   such that the following holds. For every $f\in W_0(n)$ and $u\in\mathbb{R}^m$, the function $h_u$
--   defined by
--
--   $$
--       h_u(v)=f(\pi(u,v))
--   $$
--
--   is in $W_0(l)$ with
--
--   $$
--       \|h_u\|_{W_0}\le C_{\text{W\_0 fiber integrals},\pi,1} \|f\|_{W_0}\, .
--   $$
--
--   The function $g:\mathbb{R}^m\to \mathbb{C}$ defined by
--
--   $$
--   g(u) = \int_{\mathbb{R}^l} f(\pi(u,v)) \,dv= \int_{\mathbb{R}^l} h_u(v) \,dv
--   $$
--
--   is in $W_0(m)$ with
--
--   $$
--       \|g\|_{W_0}\le C_{\text{W\_0 fiber integrals},\pi,2}  \|f\|_{W_0}\, .
--   $$
--
--   See also
--   `Auto.exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2301-L2383
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2301-L2383

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound
    {m l n : ℕ} {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (π : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f : EuclideanSpace ℝ (Fin n) → K, MemW0 f →
      (∀ u : EuclideanSpace ℝ (Fin m),
        MemW0 (fun v : EuclideanSpace ℝ (Fin l) => f (π (u, v))) ∧
        (∫ v, wienerEnvelope (fun v : EuclideanSpace ℝ (Fin l) => f (π (u, v))) 1 v) ≤
          C₁ * ∫ y, wienerEnvelope f 1 y) ∧
      MemW0 (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, f (π (u, v))) ∧
      (∫ u, wienerEnvelope (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, f (π (u, v))) 1 u) ≤
        C₂ * ∫ y, wienerEnvelope f 1 y := by sorry
