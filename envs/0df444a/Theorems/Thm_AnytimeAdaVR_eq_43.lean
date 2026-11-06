-- Prove2me | Theorems.Thm_AnytimeAdaVR_eq_43
-- name    : AnytimeAdaVR.eq_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:05.589477+00:00
-- url     : https://prove2.me/theorems/1b770a53-c331-49c7-9ce5-762ac32de4ea
-- title:
--   App. C.4 (43) — $\mathbb E\,G_\infty^2\le 2L(\Delta_f+c(9\log K+2))$
-- statement:
--   Under the assumptions of App. C (Assumptions 1 and 2; for M also average smoothness with $\bar L$, and $\Lambda=L$ for S, $\Lambda=\bar L$ for M), let $G_\infty$ be the supremum of $\|\nabla f(z)\|$ over every point $z$ visited by the S or M path from $x_{\mathrm{init}}$, that is, over the iterates $x_{j,1},\dots,x_{j,b_j+1}$ of every block $j$. Then
--   $$
--   \mathbb E\,G_\infty^2\le 2L\big(\Delta_f+c(9\log K+2)\big)<\infty,
--   $$
--   with $c=E+L/2$, $E=4\sqrt{\sigma^2+\Lambda^2}$ and $K$ from (41). No bounded-gradient assumption is used; the bound controls the labels of blocks of length two.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: fresh independent samples → the path runs on an i.i.d. sample stream ℕ → Ξ of law μ (Measure.infinitePi); reason: the probability model of p.4 for one path; same law
--   - encoding: blocks indexed j = 1, 2, … with a_1 = 1, b_1 = 2 → 0-based block index j = 0, 1, … (paramSeq / smState at j is the paper's block j + 1); reason: index shift only
--   - encoding: G_∞: the supremum of gradient norms over the countable sequence of iterates → ⨆ over blocks j and points x_{j,1}, …, x_{j,b_j+1} of ‖∇f‖ₑ in ℝ≥0∞; reason: the iterates of the path are exactly these points
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.4, eq. (43), p.22

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_smState__9c32e5
import Definitions.Def_AnytimeAdaVR_coefV

namespace AnytimeAdaVR

open MeasureTheory

/-- **App. C.4, eq. (43): the gradients visited by the path.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.4, p.22: "Let G_∞ be
the supremum of gradient norms over the countable sequence of iterates. Combining the last three
displays gives E G²_∞ ≤ 2L(∆f + c(9 log K + 2)) < ∞", with `c = E + L/2`, `E = 4√(σ² + Λ²)` and
`K` from (41). Assumptions as in App. B–C (`Λ = L` for S; Assumption 3 with `Λ = L̄` for M).

For the S or M path from `xinit` on i.i.d. samples of law `μ`, `G_∞` is the supremum of
`‖∇f(x_{j,t})‖` over every block `j` and every visited point `x_{j,t}`, `t = 1, …, b_j + 1`, and
`E G_∞² ≤ V_Λ = 2L(∆f + c_Λ(9 log K_Λ + 2))`.

**Formalization Note.** Block `j` (0-based) starts from `smState … j` and reads the samples
`ξ (off_j + i)`; `(blockSeq … s).1 = x_{j,s+1}`, so `s = 0, …, b_j` lists `x_{j,1}, …, x_{j,b_j+1}`.
`G_∞` is an `ℝ≥0∞` supremum and the expectation a lower integral. -/
theorem eq_43 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)}
    {xinit : EuclideanSpace ℝ (Fin d)} {L Δf σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA1 : Assumption1 f L Δf xinit)
    (hA2 : Assumption2 f g μ σ)
    (k : SMKind) (Λ : ℝ) (hΛ : (k = .S ∧ Λ = L) ∨ (k = .M ∧ AvgSmooth g μ Λ)) :
    ∫⁻ ξ, (⨆ j, ⨆ s ∈ Finset.range ((smState k g xinit ξ j).b + 1),
        ‖gradient f (blockSeq k g (smState k g xinit ξ j).x (smState k g xinit ξ j).a
          (smState k g xinit ξ j).b (fun i => ξ ((smState k g xinit ξ j).off + i)) s).1‖ₑ) ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => μ) ≤ ENNReal.ofReal (coefV Δf L σ Λ) := by sorry

end AnytimeAdaVR
