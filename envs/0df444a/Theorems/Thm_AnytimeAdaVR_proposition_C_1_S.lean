-- Prove2me | Theorems.Thm_AnytimeAdaVR_proposition_C_1_S
-- name    : AnytimeAdaVR.proposition_C_1_S
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:00.408012+00:00
-- url     : https://prove2.me/theorems/5ed54edd-e3a8-4c0b-b85a-fdd5ad6f84b9
-- title:
--   Proposition C.1 (S path) with App. G.1 — $\mathbb E\|\nabla f(R_{S,N})\|\le C_{1/4}(L)\,N^{-1/4}$
-- statement:
--   Assume Assumptions 1 and 2, and let the stochastic gradient be jointly measurable. Run the continuing S path from $x_{\mathrm{init}}$ with fresh samples and an independent reservoir. For every deterministic integer $N\ge1$, the report $R_{S,N}$ after $N$ local queries satisfies
--   $$
--   \mathbb E\,\|\nabla f(R_{S,N})\|\le C_{1/4}(L)\,N^{-1/4},
--   $$
--   where $C_\gamma(\Lambda)=12\sqrt{A_\Lambda V_\Lambda}+16\sqrt2\,9^\gamma(4+E_\Lambda)A_\Lambda$ is the explicit coefficient of App. G.1. In particular $\mathbb E\|\nabla f(R_{S,N})\|=O(N^{-1/4})$, which is Proposition C.1 for the S path. The bound includes interruptions inside blocks and paired queries.
--
--   **Formalization Note** $N$ counts local queries of the path, including both queries of an M pair.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: fresh independent samples, and reservoir coins independent of the samples → the path runs on an i.i.d. sample stream of law μ (Measure.infinitePi) and i.i.d. uniform coins on [0,1] (Measure.infinitePi of volume), combined by Measure.prod; reason: the probability model of pp.4 and 8 for one path; same law
--   - generalization: E‖∇f(R_S,N)‖ = O(N^-1/4) with a constant depending only on (∆f, L, σ, Λ) → the explicit bound C_1/4(L)·N^-1/4; reason: the explicit coefficient of App. G.1 (p.30) is one admissible O-constant, so the Lean statement implies (37); it is the form the paper proves and uses in Proposition E.1
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C, Proposition C.1, eq. (37), p.19; App. G.1, p.30

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_smReport
import Definitions.Def_AnytimeAdaVR_coefCgamma

namespace AnytimeAdaVR

open MeasureTheory

/-- **Proposition C.1, S path, with the explicit App. G.1 coefficient.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C, p.19,
eq. (37): "For every deterministic integer N ≥ 1, the S and M reports satisfy E‖∇f(R_{S,N})‖ = O(N^{−1/4}),
E‖∇f(R_{M,N})‖ = O(N^{−1/3}). The first bound uses objective smoothness and bounded variance. The second
additionally uses average smoothness. The bounds include interruptions inside blocks and paired
queries." and App. G.1, p.30: "E‖∇f(R_{S,N})‖ ≤ S N^{−1/4}, E‖∇f(R_{M,N})‖ ≤ M N^{−1/3}. Here
S := C_{1/4}(L) and M := C_{1/3}(L̄); the M inequality requires average smoothness", with
`C_γ(Λ)` from (63).

This item is the S half: under objective smoothness and bounded variance, for every `N ≥ 1`, the report of the S path after `N` local
queries satisfies `E‖∇f(R_{S,N})‖ ≤ S := C_{1/4}(L) · N^{−1 / 4}`.

**Formalization Note.** The path runs on an i.i.d. sample stream of law `μ` and independent uniform
reservoir coins (`Measure.infinitePi` of each, then `Measure.prod`). `N` counts local queries,
including both queries of an M pair, so interruptions inside blocks and pairs are covered. The
expectation is a lower integral; the stochastic gradient is jointly measurable. -/
theorem proposition_C_1_S {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)}
    {xinit : EuclideanSpace ℝ (Fin d)} {L Δf σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA1 : Assumption1 f L Δf xinit)
    (hA2 : Assumption2 f g μ σ)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫⁻ p, ‖gradient f (smReport .S g xinit p.1 p.2 N)‖ₑ
        ∂((Measure.infinitePi fun _ : ℕ => μ).prod
          (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))) ≤
      ENNReal.ofReal (coefCgamma (1 / 4) Δf L σ L * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by sorry

end AnytimeAdaVR
