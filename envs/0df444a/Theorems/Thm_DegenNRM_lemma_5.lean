-- Prove2me | Theorems.Thm_DegenNRM_lemma_5
-- name    : DegenNRM.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:34.843975+00:00
-- url     : https://prove2.me/theorems/68d1b7ae-425c-4f3b-8d30-990c28361c32
-- title:
--   Lemma 5 — the myopic regret in Case (i), where the query is always accepted (corrected: $8\kappa_1^2\log s/(\alpha s)$ in place of $2\log s/(\alpha s)$)
-- statement:
--   Assume Assumption 1 with constant $\alpha$. Fix remaining capacities $c\ge0$, $s$ periods left ($s=T-t+1$) and the type $j$ of the arriving query. Let $\hat q^*$ be an optimal solution of (13) at $(c,s)$ (the one Algorithm 2 uses), and let $\tilde q^*_t=\tilde q^*(\tilde d_{t+1})$ be, for every count vector $\tilde d_{t+1}$ of the $s-1$ later arrivals, an optimal solution of (12) at $(c,\tilde d_t)$, $\tilde d_t=\tilde d_{t+1}+e_j$, such that on the good event $\mathcal G$
--   $$\|\hat q^*-\tilde q^*_t\|_\infty\le\kappa_1\max_{k\in[n]}\Big|\frac{\tilde d_{k,t}}{s}-p_k\Big|$$
--   (the bound of Lemma 4). Write $\mathrm{Myopic}_t(\pi,c,\mathcal G)$ for the myopic regret (19) on $\mathcal G$ of Algorithm 1 with the estimator of Algorithm 2, and $\kappa_1$ for (15).
--
--   Suppose Case (i) holds, $\hat q^*_j\ge1-2\kappa_1\sqrt{\log s/s}$, and $s\ge s_0$ for some $s_0$ with $s_0/\log s_0\ge16\kappa_1^2$ and $s_0\ge2\max_k\{1/p_k\}$. Then
--   $$\mathrm{Myopic}_t(\pi,c,\mathcal G)\le\frac{8\kappa_1^2\log s}{\alpha s}+\frac2\alpha\,\mathbb E\big[(\tilde q^*_{j,t}-\hat q^*_j)^2\big]+\frac2\alpha\,\mathbb E\Big[\frac1{\tilde d_{j,t+1}}\,\Big|\,\mathcal G\Big].$$
--
--   Summed over periods, this bounds the regret caused by always accepting a type whose fluid acceptance probability is close to $1$.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - reading: F_j⁻¹, the inverse distribution function (not defined in the paper) → F_j⁻¹(q) = inf{r ∈ [l_j, u_j] : F_j((−∞, r]) ≥ q}; reason: the standard generalized inverse, restricted to the reward interval (reading R5)
--   - reading: κ₁ = max_j{1/p_j}·(m + 2n)·āⁿ with ā not defined → ā = max_j (‖a_j‖₂² + 2)^{1/2}; reason: reading R1: the largest column norm of [A; I_n; −I_n], which the proof of Lemma 4 (p.43) bounds; the alternative max_j ‖a_j‖₂ makes Lemma 4 false (m = 1, n = 2, a = (0.01, 0), p = (1/2, 1/2), U[0,1] rewards, c = 0.4, s = 100, d = (40, 60))
--   - encoding: log → Real.log (natural logarithm; log 0 = log 1 = 0); reason: the paper's log is natural (Hoeffding step, p.16)
--   - reading: Myopic_t(π, c, G) (19) averages over the type j_t, while the case condition is a condition on q̂*_{j_t,t} → the lemma for a fixed arriving type j_t = j, the expectation over the s − 1 later arrivals (a path under the arrival law); reason: reading R9: the case condition depends on j_t, so the lemma is per type; Theorem 1's proof averages it over j_t
--   - reading: q̃*_t, 'one optimal solution' of (12) at (c, d̃_t), related to q̂* through (18): |q̃*_{j,t} − q̂*_{j,t}| ≤ κ₁ max_{j′}|p_{j′} − d̃_{j′,t+1}/(s−1)| → q̃*_t(D) optimal for (12) at (c, D + e_j) for every count vector D of the s − 1 later arrivals, and on G it satisfies Lemma 4's bound ‖q̂* − q̃*‖∞ ≤ κ₁ max_k |d̃_{k,t}/s − p_k| with d̃_t = D + e_j; reason: (18) is stated 'following Lemma 4' (p.16), but as printed it compares d̃_{t+1}/(s−1) with p and can be unsatisfiable: m = 1, n = 2, a = (1, 2), p = (1/2, 1/2), U[0,1] rewards, c = s, s odd and D = ((s−1)/2, (s−1)/2) ∈ G force q̃* = q̂*, yet the unique optima differ (q̂*_1 = 4/5, q̃*_1 = 1 − (s−1)/(5s−3)); Lemma 4's own bound at d̃_t is satisfiable by Lemma 4
--   - reading: q^π_{j,t}, 'the ex-ante probability that query t will be served by the online policy π' (p.16), set to 1, 0 and q̂*_{j,t} in Cases (i)–(iii) → F_j([M̂, ∞)) if c ≥ a_j componentwise and 0 otherwise, with M̂ the estimator of Algorithm 2; reason: the definition on p.16; it equals the case values except for a point-mass type in Case (iii), where Algorithm 2 accepts with probability 1
--   - encoding: P(G)·E[· | G] and E[· | G] → ∫_G · and (∫_G ·)/P(G) (0 when P(G) = 0); 1/0 = 0; reason: Lean conventions; on G the count d̃_{j,t+1} is positive under the lemma's hypotheses
--   - encoding: d̃_{t+1}, the type counts of the s − 1 later arrivals, d̃_t = d̃_{t+1} + e_{j_t} → counts of a path of s − 1 periods under the product of the arrival law; q̃*_t a function of these counts; reason: the future arrivals enter only through their counts; any function of the counts is measurable
--   - correction: the first term 2 log s / (α·s) of the bound → 8κ₁² log s / (α·s); reason: the printed bound is false: n = m = 1, a₁ = 1, F₁ = U[0,1] (α = 1, κ₁ = 3√3), s = s₀ = 4000 (s₀/log s₀ ≈ 482 ≥ 432 = 16κ₁²), c = s(1 − 2κ₁√(log s/s)) ≈ 2107.1, so q̂* = q̃* = c/s is on the Case (i) boundary; then Myopic_t(π, c, G) ≈ 0.112 > 0.0046 ≈ the printed right side. The proof's step (88) uses (1 − q̂*)² ≤ log s/s, but Case (i) gives only (1 − q̂*)² ≤ 4κ₁² log s/s, which yields 8κ₁² (paper.md proof gap 2)
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 5, (21), p.17; proof pp.46–47

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_IsQuantOpt
import Definitions.Def_DegenNRM_myopicGood

open MeasureTheory

namespace DegenNRM

/-- **Lemma 5, corrected: the myopic regret in Case (i)** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, Lemma 5, (21), p.17).

In Case (i), `q̂*_{j,t} ≥ 1 - 2κ₁ √(log s / s)`, as long as `s ≥ s₀` for an `s₀` with
`s₀ / log s₀ ≥ 16κ₁²` and `s₀ ≥ 2 max_j {1/p_j}`,

`Myopic_t(π, c, G) ≤ 8κ₁² log s / (α s) + (2/α) E[(q̃*_{j,t} - q̂*_{j,t})²]
  + (2/α) E[1 / d̃_{j,t+1} | G]`.

**Correction.** The printed first term is `2 log s / (α s)`. That is false: take `n = m = 1`,
`a₁ = 1`, `F₁ = U[0,1]` (`α = 1`, `κ₁ = 3√3`), `s = s₀ = 4000` (`s₀/log s₀ ≈ 482 ≥ 432 = 16κ₁²`)
and `c = s(1 - 2κ₁√(log s/s)) ≈ 2107.1`, so that `q̂* = q̃* = c/s` sits on the Case (i)
boundary. Then `Myopic_t(π, c, G) ≈ 0.112` while the printed right side is `≈ 0.0046`. The
proof's last step (88) uses `(1 - q̂*)² ≤ log s / s`, but Case (i) only gives
`(1 - q̂*)² ≤ 4κ₁² log s / s`; with that bound the proof yields the coefficient `8κ₁²`.

**Formalization Note.** Reading R9 of the mission: the lemma is stated for a fixed remaining
capacity `c ≥ 0`, `s = T - t + 1` periods left and arriving type `j_t = j`; the expectation is
over the `s - 1` later arrivals (a sample path under `pathLaw inst (s - 1)`, whose type counts
are `D = d̃_{t+1}`). `qh = q̂*_t` is an optimal solution of (13) at `(c, s)` (the one Algorithm 2
uses) and `qt D = q̃*_t` an optimal solution of (12) at `(c, d̃_t)`, `d̃_t = D + e_j`, chosen as
in Lemma 4: on `G` it satisfies Lemma 4's bound `‖q̂* − q̃*‖_∞ ≤ κ₁ max_k |d̃_{k,t}/s − p_k|`.
`q^π_{j,t}` is the acceptance probability of the policy (`acceptProb`). `E[X | G]` is
`condMean`, `log` is `Real.log`, and `1/0 = 0` in Lean (on `G` the count `d̃_{j,t+1}` is
positive under the hypotheses). -/
theorem lemma_5 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (s : ℕ) (j : Fin n)
    (qh : Fin n → ℝ) (hqh : IsFluidOpt inst c (s : ℝ) qh)
    (qt : (Fin n → ℕ) → (Fin n → ℝ))
    (hqt : ∀ D : Fin n → ℕ, ∑ k, D k = s - 1 →
      IsQuantOpt inst c (fun k => (D k : ℝ) + if k = j then 1 else 0) (qt D))
    (hlem4 : ∀ D ∈ goodEvent inst s,
      ‖qh - qt D‖ ≤ kappa1 inst * ‖fun k => ((D k : ℝ) + if k = j then 1 else 0) / s - inst.p k‖)
    (hcase : 1 - 2 * kappa1 inst * Real.sqrt (Real.log s / s) ≤ qh j)
    (s₀ : ℝ) (hs₀ : 16 * kappa1 inst ^ 2 ≤ s₀ / Real.log s₀)
    (hs₀p : 2 * (⨆ k : Fin n, 1 / inst.p k) ≤ s₀) (hs : s₀ ≤ s) :
    myopicGood inst c s j qh qt ≤
      8 * kappa1 inst ^ 2 * Real.log s / (α * s)
        + 2 / α * ∫ ω, (qt (typeCount ω) j - qh j) ^ 2 ∂(pathLaw inst (s - 1))
        + 2 / α * condMean (pathLaw inst (s - 1)) {ω | typeCount ω ∈ goodEvent inst s}
            (fun ω => 1 / (typeCount ω j : ℝ)) := by sorry

end DegenNRM
