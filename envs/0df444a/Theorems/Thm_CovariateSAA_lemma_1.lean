-- Prove2me | Theorems.Thm_CovariateSAA_lemma_1
-- name    : CovariateSAA.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:53.433619+00:00
-- url     : https://prove2.me/theorems/12728e11-4e0a-47e6-a427-e63ed485e446
-- title:
--   Lemma 1 — $\sup_{z}|\hat g^{ER}_n(z;x)-g^*_n(z;x)|\le(\sup_z L(z))\,\frac1n\sum_i\|\tilde\varepsilon^i_n(x)\|$
-- statement:
--   Let $\mathcal Y\subseteq\mathbb R^{d_y}$ be convex with orthogonal projection $\operatorname{proj}_{\mathcal Y}$, and let the cost $c$ satisfy Assumption 1: $|c(z,\bar y)-c(z,y)|\le L(z)\|\bar y-y\|$ for all $z\in\mathcal Z$ and $y,\bar y\in\mathcal Y$, with $L(z)\ge0$ and $\sup_{z\in\mathcal Z}L(z)<+\infty$. Fix a sample size $n$, a realization of the data and a covariate value $x$ such that the FI-SAA scenarios $f^*(x)+Q^*(x)\varepsilon^i$, $i\in[n]$, lie in $\mathcal Y$. Then
--   $$
--   \sup_{z\in\mathcal Z}\bigl|\hat g^{ER}_n(z;x)-g^*_n(z;x)\bigr| \le \Bigl(\sup_{z\in\mathcal Z}L(z)\Bigr)\Bigl(\frac1n\sum_{i=1}^n\|\tilde\varepsilon^i_n(x)\|\Bigr),
--   $$
--   where $\tilde\varepsilon^i_n(x)$ is the difference between the $i$-th ER-SAA scenario $\hat f_n(x)+\hat Q_n(x)\hat\varepsilon^i_n$ and the $i$-th FI-SAA scenario $f^*(x)+Q^*(x)\varepsilon^i$.
--
--   The lemma reduces the uniform distance between the ER-SAA and the full-information SAA objectives to the mean deviation of the scenarios, which Lemma 2 then bounds by regression errors.
--
--   Differences from the source:
--   - reading: c is defined on 𝒵 × 𝒴 and the FI-SAA scenarios f*(x) + Q*(x)εⁱ lie in 𝒴 (p.5, p.6) → c is defined on ℝ^{d_z} × ℝ^{d_y} and the scenarios lying in 𝒴 is a hypothesis; reason: the paper needs it for g*_n to be defined and states it on p.6; Lean functions are total.
--   - generalization: standing assumptions of pp.5–6 (𝒵 nonempty compact, 𝒴 closed, the data model, Q* positive definite, Q̂_n nonsingular) → only 𝒴 convex with its nearest-point projection, Assumption 1 and the scenarios in 𝒴 for the given realization; reason: the inequality is deterministic and its proof uses only these; the paper's setting is an instance.
--   - encoding: sup_{z∈𝒵}|ĝ^ER_n(z; x) − g*_n(z; x)| ≤ (sup_{z∈𝒵} L(z))·mean → for every z ∈ 𝒵, |ĝ^ER_n(z; x) − g*_n(z; x)| ≤ sSup (L  𝒵)·mean; reason: a supremum is bounded by a number iff every term is; sup L is finite by Assumption 1.
--   - encoding: Lipschitz constant L(z) (Assumption 1, p.9) → Assumption1 requires 0 ≤ L(z) for z ∈ 𝒵; reason: a Lipschitz constant is nonnegative; the clause only excludes negative values, possible when 𝒴 has at most one point, where the paper's L ≥ 0 serves equally.
--   - encoding: vectors in ℝ^d with the Euclidean norm, matrices Q*(x), Q̂_n(x) with the induced matrix norm, samples i ∈ [n], proj_𝒴 the orthogonal projection → EuclideanSpace ℝ (Fin d), continuous linear maps with the operator norm, i : Fin n (0-indexed), a nearest-point map onto 𝒴; reason: Lean convention; same instances.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Lemma 1, p.9 (with Assumption 1, p.9; deviation sequence, p.9)

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_CovariateSAA_Assumptions

namespace CovariateSAA

/-- **Lemma 1** (Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average Approximation with
Covariate Information*, arXiv:2207.13554v1, p.9). Suppose Assumption 1 holds. Then
`sup_{z ∈ 𝒵} |ĝ^ER_n(z; x) − g*_n(z; x)| ≤ (sup_{z ∈ 𝒵} L(z)) ((1/n) Σ_{i=1}^n ‖ε̃ⁱ_n(x)‖)`.

The statement is deterministic: it holds for every sample size `n`, sample point `ω` and
covariate `x`, given that the FI-SAA scenarios `f*(x) + Q*(x)εⁱ` lie in `𝒴` (the paper's cost
`c` is defined on `𝒵 × 𝒴` only, and p.6 states these scenarios are contained in `𝒴`).

**Formalization Note** `proj` is the orthogonal projection onto the nonempty convex set `𝒴`
(p.5–6), given as a nearest-point map. The supremum over `𝒵` on the left is written as a bound
for every `z ∈ 𝒵`; `sup_{z∈𝒵} L(z)` is `sSup (L '' Z)`, finite by Assumption 1. -/
theorem lemma_1 {dx dy dz : ℕ} {Ω : Type*} (D : Data dx dy Ω) (c : Vec dz → Vec dy → ℝ)
    (Z : Set (Vec dz)) (𝒴 : Set (Vec dy)) (proj : Vec dy → Vec dy)
    (h𝒴 : Convex ℝ 𝒴) (hproj : ResidualsDRO.Wass.IsNearestPointProj 𝒴 proj)
    (L : Vec dz → ℝ) (hA1 : Assumption1 c Z 𝒴 L)
    (x : Vec dx) (n : ℕ) (ω : Ω) (hFI : ∀ i : Fin n, fiScenario D x ω i ∈ 𝒴) :
    ∀ z ∈ Z, |gER D c proj x n ω z - gFI D c x n ω z| ≤
      sSup (L '' Z) * empMean n (fun i => ‖epsTilde D x n ω i‖) := by sorry

end CovariateSAA
