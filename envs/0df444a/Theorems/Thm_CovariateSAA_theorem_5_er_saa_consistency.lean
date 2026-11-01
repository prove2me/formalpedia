-- Prove2me | Theorems.Thm_CovariateSAA_theorem_5_er_saa_consistency
-- name    : CovariateSAA.theorem_5_er_saa_consistency
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:34.960339+00:00
-- url     : https://prove2.me/theorems/9f5532c5-e992-43a7-be85-bea569033769
-- title:
--   Theorem 5 — the ER-SAA is consistent and asymptotically optimal: $\hat v^{ER}_n(x)\xrightarrow{p}v^*(x)$, $\mathbb D(\hat S^{ER}_n(x),S^*(x))\xrightarrow{p}0$
-- statement:
--   Consider the conditional stochastic program $v^*(x)=\min_{z\in\mathcal Z} g(z;x)$, $g(z;x)=\mathbb E[c(z,f^*(x)+Q^*(x)\varepsilon)]$, with solution set $S^*(x)$, and its empirical residuals-based SAA (4) with optimal value $\hat v^{ER}_n(x)$ and solution set $\hat S^{ER}_n(x)$. Assume the standing assumptions of the paper: $\mathcal Z$ is nonempty and compact; $\mathcal Y$ is nonempty, closed and convex; $\mathbb E|c(z,f^*(x)+Q^*(x)\varepsilon)|<+\infty$ for each $z\in\mathcal Z$ and a.e. $x$; $g(\cdot;x)$ is lower semicontinuous on $\mathcal Z$ for a.e. $x$; $\hat S^{ER}_n(x)$ is nonempty; the FI-SAA scenarios lie in $\mathcal Y$; $Q^*$ is invertible at the data. Suppose Assumptions 1 to 5 hold. Then, for $P_X$-almost every $x$,
--   $$
--   \hat v^{ER}_n(x)\xrightarrow{p}v^*(x), \qquad \mathbb D\bigl(\hat S^{ER}_n(x),S^*(x)\bigr)\xrightarrow{p}0, \qquad \sup_{z\in\hat S^{ER}_n(x)} g(z;x)\xrightarrow{p}v^*(x),
--   $$
--   where $\mathbb D(A,B)=\sup_{v\in A}\operatorname{dist}(v,B)$. The third clause means: for every $\delta>0$, $P\{\exists z\in\hat S^{ER}_n(x): g(z;x)>v^*(x)+\delta\}\to0$.
--
--   The theorem says that the ER-SAA, built from any consistent regression procedure in the heteroscedastic model, recovers the optimal value and the optimal solutions of the true conditional problem and its solutions are asymptotically optimal.
--
--   Differences from the source:
--   - reading: c is defined on 𝒵 × 𝒴 and the FI-SAA scenarios f*(x) + Q*(x)εⁱ lie in 𝒴 (p.5, p.6) → c is defined on ℝ^{d_z} × ℝ^{d_y}; hypothesis: for P_X-a.e. x, almost surely every scenario f*(x) + Q*(x)εⁱ lies in 𝒴; reason: the paper needs it for g*_n to be defined and states it on p.6; under the paper's model it holds almost surely.
--   - generalization: data (yⁱ, xⁱ) drawn from the model Y = f*(X) + Q*(X)ε with ε zero-mean, independent of X, E[εεᵀ] = I; εⁱ := [Q*(xⁱ)]⁻¹(yⁱ − f*(xⁱ)) → xⁱ, εⁱ arbitrary random variables on a probability space (Ω, P), yⁱ := f*(xⁱ) + Q*(xⁱ)εⁱ, f̂_n, Q̂_n arbitrary random functions, P_X and P_ε any probability measures not tied to the data; reason: the proof uses the data only through Assumptions 2–5; the paper's data process is an instance and its εⁱ agree with these under invertibility of Q*(xⁱ).
--   - generalization: Q̂_n nonsingular with [Q̂_n(x̄)]⁻¹ ≻ 0 (p.6, Lemma 2) → no assumption on Q̂_n; [·]⁻¹ is Ring.inverse (0 on singular operators); reason: the argument holds for any operator in place of [Q̂_n(xⁱ)]⁻¹; nonsingular Q̂_n are an instance.
--   - generalization: Q*(x̄) ≻ 0 for every x̄ in the support 𝒳 (p.5) → Q*(xⁱ) invertible at the data points (almost surely); reason: the proof uses only [Q*(xⁱ)]⁻¹Q*(xⁱ) = I; positive definiteness on 𝒳 and xⁱ ∈ 𝒳 imply it.
--   - generalization: Assumptions 3 and 4: empirical moments →p E[‖Q*(X)‖⁴], E[‖[Q*(X)]⁻¹‖²], E[‖ε‖⁴] → the empirical moments converge in probability to some finite real constant; reason: the paper's (finite) expectations are such constants; the proof only uses boundedness in probability.
--   - generalization: all functions, sets and selections measurable (p.8) → no measurability hypothesis; P is applied to arbitrary sets as an outer measure; reason: the proof uses only monotonicity and subadditivity of P; under the paper's measurability the statements coincide.
--   - generalization: Ŝ^ER_n(x) nonempty for a.e. x (p.6) → for P_X-a.e. x and every n, Ŝ^ER_n(x) nonempty almost surely; reason: a weaker hypothesis that the proof suffices with; the paper's assumption implies it.
--   - encoding: sup_{z∈Ŝ^ER_n(x)} g(z; x) →p v*(x) → ∀ δ > 0, P{∃ z ∈ Ŝ^ER_n(x), g(z; x) > v*(x) + δ} → 0; reason: g(·; x) ≥ v*(x) on Ŝ^ER_n(x) ⊆ 𝒵, so the two say the same; avoids a real ⨆ that Lean sets to 0 on unbounded sets.
--   - encoding: v*(x), v̂^ER_n(x) minima, S*(x), Ŝ^ER_n(x) argmin sets, 𝔻(A, B) = sup_{v∈A} dist(v, B) → sInf of the image, argmin set, real sSup of Metric.infDist over A; reason: the minima are attained (g(·; x) l.s.c. on compact 𝒵; Ŝ^ER_n(x) nonempty a.s.) and 𝔻 is bounded (𝒵 compact, S*(x) ≠ ∅), so the values agree off a null event.
--   - encoding: Lipschitz constant L(z) (Assumption 1, p.9) → Assumption1 requires 0 ≤ L(z) for z ∈ 𝒵; reason: a Lipschitz constant is nonnegative; the clause only excludes negative values, possible when 𝒴 has at most one point, where the paper's L ≥ 0 serves equally.
--   - encoding: vectors in ℝ^d with the Euclidean norm, matrices Q*(x), Q̂_n(x) with the induced matrix norm, samples i ∈ [n], proj_𝒴 the orthogonal projection → EuclideanSpace ℝ (Fin d), continuous linear maps with the operator norm, i : Fin n (0-indexed), a nearest-point map onto 𝒴; reason: Lean convention; same instances.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Theorem 5, p.13 (Assumptions 1–5, pp.9, 11; standing assumptions pp.5–6; proof p.28)

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_CovariateSAA_Assumptions

open MeasureTheory Filter Topology

namespace CovariateSAA

/-- **Theorem 5** (Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average Approximation with
Covariate Information*, arXiv:2207.13554v1, p.13). Suppose Assumptions 1 to 5 hold. Then
`v̂^ER_n(x) →p v*(x)`, `𝔻(Ŝ^ER_n(x), S*(x)) →p 0`, and `sup_{z ∈ Ŝ^ER_n(x)} g(z; x) →p v*(x)`
for a.e. `x ∈ 𝒳`.

Standing assumptions of pp.5–6 carried as hypotheses: `𝒵` nonempty compact; `𝒴` nonempty,
closed and convex with orthogonal projection `proj`; `E|c(z, f*(x) + Q*(x)ε)| < ∞` for each
`z ∈ 𝒵` and a.e. `x`; `g(·; x)` lower semicontinuous on `𝒵` for a.e. `x`; `Ŝ^ER_n(x)` nonempty (almost surely) for
a.e. `x`; the FI-SAA scenarios lie in `𝒴`; `Q*(xⁱ)` invertible at the data.

**Formalization Note** `→p` is `TendstoInMeasure` (outer measure, no measurability assumed).
The third clause is in event form: since `g(·; x) ≥ v*(x)` on `Ŝ^ER_n(x) ⊆ 𝒵`,
`sup_{Ŝ^ER_n(x)} g(·; x) →p v*(x)` says exactly that for every `δ > 0`,
`P{∃ z ∈ Ŝ^ER_n(x), g(z; x) > v*(x) + δ} → 0`; this avoids a real `⨆` of a possibly unbounded
set. The data are arbitrary random objects on `(Ω, P)`; "a.e. `x`" is `P_X`-a.e. -/
theorem theorem_5_er_saa_consistency {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PX : Measure (Vec dx)) [IsProbabilityMeasure PX]
    (Pε : Measure (Vec dy)) [IsProbabilityMeasure Pε]
    (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (Z : Set (Vec dz))
    (𝒴 : Set (Vec dy)) (proj : Vec dy → Vec dy) (L : Vec dz → ℝ)
    (hZc : IsCompact Z) (hZne : Z.Nonempty)
    (h𝒴ne : 𝒴.Nonempty) (h𝒴cl : IsClosed 𝒴) (h𝒴cv : Convex ℝ 𝒴)
    (hproj : ResidualsDRO.Wass.IsNearestPointProj 𝒴 proj)
    (hint : ∀ z ∈ Z, ∀ᵐ x ∂PX, Integrable (fun e => c z (D.fstar x + D.Qstar x e)) Pε)
    (hlsc : ∀ᵐ x ∂PX, LowerSemicontinuousOn (gTrue D Pε c x) Z)
    (hSER : ∀ᵐ x ∂PX, ∀ n : ℕ, ∀ᵐ ω ∂P, (SER D c proj Z x n ω).Nonempty)
    (hFI : ∀ᵐ x ∂PX, ∀ᵐ ω ∂P, ∀ i : ℕ, fiScenario D x ω i ∈ 𝒴)
    (hQ : ∀ᵐ ω ∂P, ∀ i : ℕ, IsUnit (D.Qstar (D.xs i ω)))
    (hA1 : Assumption1 c Z 𝒴 L) (hA2 : Assumption2 P PX Pε D c Z)
    (hA3 : Assumption3 P D) (hA4 : Assumption4 P D) (hA5 : Assumption5 P PX D) :
    ∀ᵐ x ∂PX,
      TendstoInMeasure P (fun n ω => vER D c proj Z x n ω) atTop
        (fun _ => vStar D Pε c Z x) ∧
      TendstoInMeasure P (fun n ω => deviation (SER D c proj Z x n ω) (SStar D Pε c Z x)) atTop
        (fun _ => 0) ∧
      ∀ δ : ℝ, 0 < δ → Tendsto
        (fun n => P {ω | ∃ z ∈ SER D c proj Z x n ω, vStar D Pε c Z x + δ < gTrue D Pε c x z})
        atTop (𝓝 0) := by sorry

end CovariateSAA
