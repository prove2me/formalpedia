-- Prove2me | Theorems.Thm_CovariateSAA_proposition_4
-- name    : CovariateSAA.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:30:02.310156+00:00
-- url     : https://prove2.me/theorems/b683ad4e-9c45-4b8c-a34d-8d7a4c1041e5
-- title:
--   Proposition 4 — ER-SAA objectives converge to $g(\cdot;x)$ uniformly on $\mathcal Z$ in probability
-- statement:
--   Consider the covariate model $Y=f^*(X)+Q^*(X)\varepsilon$ with a nonempty compact feasible set $\mathcal Z$, a nonempty closed convex support $\mathcal Y$ with orthogonal projection $\operatorname{proj}_{\mathcal Y}$, FI-SAA scenarios $f^*(x)+Q^*(x)\varepsilon^i$ in $\mathcal Y$, and $Q^*$ invertible at the data. Suppose Assumptions 1 through 5 hold. Then, for $P_X$-almost every $x$, the ER-SAA objectives converge in probability to the true objective uniformly on $\mathcal Z$:
--   $$
--   \sup_{z\in\mathcal Z}\bigl|\hat g^{ER}_n(z;x)-g(z;x)\bigr|\xrightarrow{p}0,
--   $$
--   that is, $P\{\exists z\in\mathcal Z:|\hat g^{ER}_n(z;x)-g(z;x)|>\kappa\}\to0$ for every $\kappa>0$.
--
--   This is the uniform law of large numbers for the data-driven problem (4); Theorem 5 derives the convergence of optimal values and solutions from it.
--
--   Differences from the source:
--   - reading: c is defined on 𝒵 × 𝒴 and the FI-SAA scenarios f*(x) + Q*(x)εⁱ lie in 𝒴 (p.5, p.6) → c is defined on ℝ^{d_z} × ℝ^{d_y}; hypothesis: for P_X-a.e. x, almost surely every scenario f*(x) + Q*(x)εⁱ lies in 𝒴; reason: the paper needs it for g*_n to be defined and states it on p.6; under the paper's model it holds almost surely.
--   - generalization: data (yⁱ, xⁱ) drawn from the model Y = f*(X) + Q*(X)ε with ε zero-mean, independent of X, E[εεᵀ] = I; εⁱ := [Q*(xⁱ)]⁻¹(yⁱ − f*(xⁱ)) → xⁱ, εⁱ arbitrary random variables on a probability space (Ω, P), yⁱ := f*(xⁱ) + Q*(xⁱ)εⁱ, f̂_n, Q̂_n arbitrary random functions, P_X and P_ε any probability measures not tied to the data; reason: the proof uses the data only through Assumptions 2–5; the paper's data process is an instance and its εⁱ agree with these under invertibility of Q*(xⁱ).
--   - generalization: Q̂_n nonsingular with [Q̂_n(x̄)]⁻¹ ≻ 0 (p.6, Lemma 2) → no assumption on Q̂_n; [·]⁻¹ is Ring.inverse (0 on singular operators); reason: the argument holds for any operator in place of [Q̂_n(xⁱ)]⁻¹; nonsingular Q̂_n are an instance.
--   - generalization: Q*(x̄) ≻ 0 for every x̄ in the support 𝒳 (p.5) → Q*(xⁱ) invertible at the data points (almost surely); reason: the proof uses only [Q*(xⁱ)]⁻¹Q*(xⁱ) = I; positive definiteness on 𝒳 and xⁱ ∈ 𝒳 imply it.
--   - generalization: Assumptions 3 and 4: empirical moments →p E[‖Q*(X)‖⁴], E[‖[Q*(X)]⁻¹‖²], E[‖ε‖⁴] → the empirical moments converge in probability to some finite real constant; reason: the paper's (finite) expectations are such constants; the proof only uses boundedness in probability.
--   - generalization: all functions, sets and selections measurable (p.8) → no measurability hypothesis; P is applied to arbitrary sets as an outer measure; reason: the proof uses only monotonicity and subadditivity of P; under the paper's measurability the statements coincide.
--   - generalization: standing assumptions E|c(z, f*(x) + Q*(x)ε)| < ∞, g(·; x) lower semicontinuous, Ŝ^ER_n(x) nonempty (pp.5–6) → not assumed; reason: the proof of Proposition 4 does not use them; the paper's setting is an instance.
--   - encoding: sup_{z∈𝒵} |h_n(z; x) − h(z; x)| →p 0 → ∀ κ > 0, P{∃ z ∈ 𝒵, |h_n(z; x) − h(z; x)| > κ} → 0; reason: the two events coincide; avoids a real ⨆ that Lean sets to 0 on unbounded sets.
--   - encoding: Lipschitz constant L(z) (Assumption 1, p.9) → Assumption1 requires 0 ≤ L(z) for z ∈ 𝒵; reason: a Lipschitz constant is nonnegative; the clause only excludes negative values, possible when 𝒴 has at most one point, where the paper's L ≥ 0 serves equally.
--   - encoding: vectors in ℝ^d with the Euclidean norm, matrices Q*(x), Q̂_n(x) with the induced matrix norm, samples i ∈ [n], proj_𝒴 the orthogonal projection → EuclideanSpace ℝ (Fin d), continuous linear maps with the operator norm, i : Fin n (0-indexed), a nearest-point map onto 𝒴; reason: Lean convention; same instances.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Proposition 4, p.12 (Assumptions 1–5, pp.9, 11; standing assumptions pp.5–6)

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_CovariateSAA_Assumptions

open MeasureTheory

namespace CovariateSAA

/-- **Proposition 4** (Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average Approximation
with Covariate Information*, arXiv:2207.13554v1, p.12). Suppose Assumptions 1 through 5 hold.
Then, for a.e. `x ∈ 𝒳`, the sequence of objective functions `ĝ^ER_n(·; x)` of the ER-SAA
problem (4) converges in probability to the objective function `g(·; x)` of the true problem (1)
uniformly on the feasible region `𝒵`.

Standing assumptions of pp.5–6 carried as hypotheses: `𝒵` nonempty compact; `𝒴` nonempty,
closed and convex with orthogonal projection `proj`; the FI-SAA scenarios lie in `𝒴`
(`c : 𝒵 × 𝒴 → ℝ`); `Q*(xⁱ)` invertible at the data (`Q*(x̄) ≻ 0` on the support of `X`).

**Formalization Note** The data `(xⁱ, εⁱ)` and the estimates are arbitrary random objects on a
probability space `(Ω, P)`; `→p` is `TendstoInMeasure` and "uniformly on `𝒵` in probability"
is `UnifTendstoInProb` (event form). "a.e. `x`" is `P_X`-a.e. -/
theorem proposition_4 {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PX : Measure (Vec dx)) [IsProbabilityMeasure PX]
    (Pε : Measure (Vec dy)) [IsProbabilityMeasure Pε]
    (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ) (Z : Set (Vec dz))
    (𝒴 : Set (Vec dy)) (proj : Vec dy → Vec dy) (L : Vec dz → ℝ)
    (hZc : IsCompact Z) (hZne : Z.Nonempty)
    (h𝒴ne : 𝒴.Nonempty) (h𝒴cl : IsClosed 𝒴) (h𝒴cv : Convex ℝ 𝒴)
    (hproj : ResidualsDRO.Wass.IsNearestPointProj 𝒴 proj)
    (hFI : ∀ᵐ x ∂PX, ∀ᵐ ω ∂P, ∀ i : ℕ, fiScenario D x ω i ∈ 𝒴)
    (hQ : ∀ᵐ ω ∂P, ∀ i : ℕ, IsUnit (D.Qstar (D.xs i ω)))
    (hA1 : Assumption1 c Z 𝒴 L) (hA2 : Assumption2 P PX Pε D c Z)
    (hA3 : Assumption3 P D) (hA4 : Assumption4 P D) (hA5 : Assumption5 P PX D) :
    ∀ᵐ x ∂PX,
      UnifTendstoInProb P (fun n ω z => gER D c proj x n ω z) (gTrue D Pε c x) Z := by sorry

end CovariateSAA
