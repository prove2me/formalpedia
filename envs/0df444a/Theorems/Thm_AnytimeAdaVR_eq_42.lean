-- Prove2me | Theorems.Thm_AnytimeAdaVR_eq_42
-- name    : AnytimeAdaVR.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:32:07.708484+00:00
-- url     : https://prove2.me/theorems/5d5c96c9-5938-4a06-9f87-3a2d61aba749
-- title:
--   App. C.3 (41)–(42) — $a_j\uparrow a_\infty$, $\mathbb E a_\infty^2\le A_\Lambda$, $\mathbb E H_\infty\le 9\log K+2$
-- statement:
--   Assume Assumptions 1 and 2; for the M path assume also average smoothness with constant $\bar L$. Put $\Lambda=L$ for S and $\Lambda=\bar L$ for M, $E=4\sqrt{\sigma^2+\Lambda^2}$, $c=E+L/2$, and
--   $$
--   K=2+\frac{\Delta_f}2+c+\frac{9c}2\log\big(\max\{1,9c/2\}\big).
--   $$
--   Let $a_j$ be the scales of the path from $x_{\mathrm{init}}$ and $u_j=(2/b_j)^{p/2}/a_j$. Then:
--
--   1. almost surely, $a_j$ is nondecreasing and converges to a finite limit $a_\infty$;
--   2. $\mathbb E\,a_\infty^2\le K^2+\tfrac14E^2(9\log K+2)$;
--   3. almost surely, $H_\infty:=\sum_{j\ge1}u_j\le 9\log a_\infty+2$;
--   4. $\mathbb E\,H_\infty\le 9\log K+2$.
--
--   The bound on $\mathbb E\,a_\infty^2$ holds uniformly over the run and drives the report rates of the S and M paths.
--
--   **Formalization Note** In item 2, $a_\infty$ is the supremum of the scales in $[0,\infty]$, which equals the limit; in item 3 the series is bounded through its partial sums; in item 4, $H_\infty$ is a sum in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: fresh independent samples → the path runs on an i.i.d. sample stream ℕ → Ξ of law μ (Measure.infinitePi); reason: the probability model of p.4 for one path; same law
--   - encoding: blocks indexed j = 1, 2, … with a_1 = 1, b_1 = 2 → 0-based block index j = 0, 1, … (paramSeq / smState at j is the paper's block j + 1); reason: index shift only
--   - encoding: a_∞ = lim a_j and H_∞ = Σ_j u_j → a_∞ as ⨆_j a_j in ℝ≥0∞ in clause 2 and as the real limit in clauses 1 and 3; H_∞ as an ℝ≥0∞ series in clause 4 and through its partial sums in clause 3; reason: a_j is nondecreasing, so the supremum is the limit; a series of nonnegative terms is the supremum of its partial sums
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.3, eqs. (41)–(42), pp.21–22

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_smState__9c32e5
import Definitions.Def_AnytimeAdaVR_coefA

namespace AnytimeAdaVR

open MeasureTheory Filter Topology

/-- **App. C.3, eqs. (41)–(42): a uniform second-moment bound for the scale.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.3,
pp.21–22: "The sequences a_{J+1}, a²_{J+1}, and H_J are nonnegative and nondecreasing. Monotone
convergence proves a_j ↑ a_∞ < ∞ almost surely, E a²_∞ ≤ K² + (1/4)E²(9 log K + 2),
H_∞ := Σ_{j≥1} u_j ≤ 9 log a_∞ + 2, E H_∞ ≤ 9 log K + 2", with
`K = 2 + ∆f/2 + c + (9c/2) log(max{1, 9c/2})` (41), `c = E + L/2`, `E = 4√(σ² + Λ²)`, and
`u_j = (2/b_j)^{p/2}/a_j` (p.19). Assumptions (App. B–C): Assumptions 1 and 2, plus Assumption 3
with `Λ = L̄` for M; `Λ = L` for S.

For the S or M path from `xinit` on i.i.d. samples of law `μ`, with scales `a_j`:
1. almost surely `a_j` is nondecreasing and converges to a finite `a_∞`;
2. `E a_∞² ≤ A_Λ = K_Λ² + (E_Λ²/4)(9 log K_Λ + 2)`;
3. almost surely every partial sum of `u_j` is at most `9 log a_∞ + 2` (so `H_∞ ≤ 9 log a_∞ + 2`);
4. `E H_∞ ≤ 9 log K_Λ + 2`.

**Formalization Note.** Blocks are 0-based (`smState … j` is the paper's block `j + 1`). `a_∞` is
the supremum `⨆ j, a_j` in `ℝ≥0∞` in (2) (equal to the limit, the sequence being nondecreasing), and
`H_∞` is the `ℝ≥0∞`-valued sum in (4). Expectations are lower integrals over the path's sample
stream (`Measure.infinitePi`). The stochastic gradient is jointly measurable. -/
theorem eq_42 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)}
    {xinit : EuclideanSpace ℝ (Fin d)} {L Δf σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA1 : Assumption1 f L Δf xinit)
    (hA2 : Assumption2 f g μ σ)
    (k : SMKind) (Λ : ℝ) (hΛ : (k = .S ∧ Λ = L) ∨ (k = .M ∧ AvgSmooth g μ Λ)) :
    let a : ℕ → (ℕ → Ξ) → ℝ := fun j ξ => (smState k g xinit ξ j).a
    let u : ℕ → (ℕ → Ξ) → ℝ := fun j ξ =>
      (match k with
        | .S => 2 / ((smState k g xinit ξ j).b : ℝ)
        | .M => Real.sqrt (2 / ((smState k g xinit ξ j).b : ℝ))) / a j ξ
    (∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => μ),
        Monotone (fun j => a j ξ) ∧ ∃ aInf : ℝ, Tendsto (fun j => a j ξ) atTop (𝓝 aInf)) ∧
    (∫⁻ ξ, (⨆ j, ENNReal.ofReal (a j ξ)) ^ 2 ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
        ENNReal.ofReal (coefA Δf L σ Λ)) ∧
    (∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => μ), ∀ aInf : ℝ,
        Tendsto (fun j => a j ξ) atTop (𝓝 aInf) →
          ∀ J, ∑ j ∈ Finset.range J, u j ξ ≤ 9 * Real.log aInf + 2) ∧
    (∫⁻ ξ, ∑' j, ENNReal.ofReal (u j ξ) ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
        ENNReal.ofReal (9 * Real.log (coefK Δf L σ Λ) + 2)) := by sorry

end AnytimeAdaVR
