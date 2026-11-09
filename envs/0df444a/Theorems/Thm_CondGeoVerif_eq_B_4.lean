-- Prove2me | Theorems.Thm_CondGeoVerif_eq_B_4
-- name    : CondGeoVerif.eq_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:38:26.400764+00:00
-- url     : https://prove2.me/theorems/e13e7f4e-fd5c-4f94-8916-1ef852ee2d11
-- title:
--   (B.3)–(B.4) — likelihood kernel $|K(V,W)-1|\le\|V^\top W\|_{\mathrm{op}}^{j+1}$
-- statement:
--   Let $k\ge1$, $0<\eta<1/2$, $a=1-2\eta$, $f$ Borel, $j\in\{0,1\}$, and let $e$ be a jointly measurable allocation with $e(u,\cdot)\in\mathcal E_j$ for every $u$. Let $Q$ be the random-noise anchor on $\mathbb R^{k+D}\times\{-1,1\}$ and $P_V,P_W$ the alternatives of orthonormal residual frames $V,W\in\mathbb R^{D\times k}$. With $r_0=af(U)$, $r_V=f(U)(1-2e(U,V^\top Z))$ and $\Delta_V=r_V-r_0$, the one-observation likelihood cross-moment satisfies
--   $$K(V,W):=\mathbb E_Q\Big[\frac{dP_V}{dQ}\frac{dP_W}{dQ}\Big]=1+\frac{\mathbb E\Delta_V(X)\Delta_W(X)}{1-a^2}=1+\mathbb E_U\mathbb E_Z[b_U(V^\top Z)b_U(W^\top Z)],$$
--   $b_u(g)=(e(u,g)-\eta)/\sqrt{\eta(1-\eta)}$ (B.3), and
--   $$|K(V,W)-1|\le\|V^\top W\|_{\mathrm{op}}^{j+1}\qquad(B.4).$$
--   Also $K(V,W)\ge0$.
--
--   Differences from the source:
--   - generalization: e from Lemma B.2 → any jointly measurable allocation with sections in E_j; reason: the paper's allocation is one such
--   - encoding: Q, P_V, P_W defined by regressions; ±1 labels → probability measures with IsLabelLaw; Boolean labels mapped to ±1 by sgn; densities as Radon–Nikodym derivatives; reason: the characterizing property determines each law; same quantities
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §B.3, p.26 (PDF p.29), eqs. (B.3), (B.4)

import Mathlib
import Definitions.Def_CondGeoVerif_hiddenErr
import Definitions.Def_CondGeoVerif_IsRotInvStiefelLaw
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif

/-- **The likelihood kernel bound (B.4), with the identities (B.3)** (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, §B.3, p.26 =
PDF p.29). Let `e` be a jointly measurable allocation with `e(u, ·) ∈ E_j` for every `u`, `Q` the
random-noise anchor and `P_V`, `P_W` the alternatives of two residual frames `V, W ∈ ℝ^{D×k}`.
With `r₀ = af(U)`, `a = 1 − 2η`, `r_V = f(U)(1 − 2e(U, VᵀZ))` and `∆_V = r_V − r₀`, the
one-observation likelihood cross-moment satisfies
`K(V, W) := E_Q[(dP_V/dQ)(dP_W/dQ)] = 1 + E∆_V(X)∆_W(X)/(1 − a²)
= 1 + E_U E_Z[b_U(VᵀZ)b_U(WᵀZ)]`, `b_u(g) = (e(u, g) − η)/√(η(1 − η))` (B.3), and with `s = j + 1`
and `R = VᵀW`, `|K(V, W) − 1| ≤ ‖VᵀW‖_op^{j+1}` (B.4). Also `K(V, W) ≥ 0`.

**Formalization Note** Labels are `Bool`; the paper's `±1` regressions are transcribed with
`sgn`. `E∆_V∆_W` is an expectation over `X ∼ N(0, I_d)`, `d = k + D`. The laws are given through
their characterizing property `IsLabelLaw`; densities are Radon–Nikodym derivatives. -/
theorem eq_B_4 {k D : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (f : Vec k → Bool) (hf : Measurable f) (j : Fin 2) (e : Vec k → Vec k → ℝ)
    (he : Measurable (fun p : Vec k × Vec k => e p.1 p.2)) (heE : ∀ u, e u ∈ errorAllocs j η k)
    (Q : ProbabilityMeasure (Vec (k + D) × Bool))
    (hQ : IsLabelLaw (Q : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (fun _ => η))
    (V W : Matrix (Fin D) (Fin k) ℝ) (hV : V ∈ stiefel D k) (hW : W ∈ stiefel D k)
    (PV PW : ProbabilityMeasure (Vec (k + D) × Bool))
    (hPV : IsLabelLaw (PV : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (hiddenErr e V))
    (hPW : IsLabelLaw (PW : Measure (Vec (k + D) × Bool)) (fun x => f (splitU x)) (hiddenErr e W)) :
    let a : ℝ := 1 - 2 * η
    let Δ : Matrix (Fin D) (Fin k) ℝ → Vec (k + D) → ℝ := fun V' x =>
      sgn (f (splitU x)) * (1 - 2 * hiddenErr e V' x) - a * sgn (f (splitU x))
    let K : ℝ := likKernel (Q : Measure (Vec (k + D) × Bool)) (PV : Measure (Vec (k + D) × Bool))
      (PW : Measure (Vec (k + D) × Bool))
    K = 1 + (∫ x, Δ V x * Δ W x ∂(gauss (k + D))) / (1 - a ^ 2) ∧
    K = 1 + ∫ u, ∫ z, normAlloc η e u (matVec Vᵀ z) * normAlloc η e u (matVec Wᵀ z)
      ∂(gauss D) ∂(gauss k) ∧
    |K - 1| ≤ opNorm (Vᵀ * W) ^ ((j : ℕ) + 1) ∧
    0 ≤ K := by sorry

end CondGeoVerif
