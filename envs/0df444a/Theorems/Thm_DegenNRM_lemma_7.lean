-- Prove2me | Theorems.Thm_DegenNRM_lemma_7
-- name    : DegenNRM.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:34.681867+00:00
-- url     : https://prove2.me/theorems/c127e7b0-7876-4417-9bf6-18602ab8ac6f
-- title:
--   Lemma 7 — the myopic regret in Case (iii), where the query is accepted above the fluid quantile
-- statement:
--   Assume Assumption 1 with constant $\alpha$. Fix remaining capacities $c\ge0$, $s$ periods left ($s=T-t+1$) and the type $j$ of the arriving query. Let $\hat q^*$ be an optimal solution of (13) at $(c,s)$ (the one Algorithm 2 uses), and let $\tilde q^*_t=\tilde q^*(\tilde d_{t+1})$ be, for every count vector $\tilde d_{t+1}$ of the $s-1$ later arrivals, an optimal solution of (12) at $(c,\tilde d_t)$, $\tilde d_t=\tilde d_{t+1}+e_j$, such that on the good event $\mathcal G$
--   $$\|\hat q^*-\tilde q^*_t\|_\infty\le\kappa_1\max_{k\in[n]}\Big|\frac{\tilde d_{k,t}}{s}-p_k\Big|$$
--   (the bound of Lemma 4). Write $\mathrm{Myopic}_t(\pi,c,\mathcal G)$ for the myopic regret (19) on $\mathcal G$ of Algorithm 1 with the estimator of Algorithm 2, and $\kappa_1$ for (15).
--
--   Suppose Case (iii) holds, $2\kappa_1\sqrt{\log s/s}\le\hat q^*_j\le1-2\kappa_1\sqrt{\log s/s}$, and $s\ge s_0$ for some $s_0$ with $s_0\log s_0\ge\frac4{\kappa_1^2}\max_k\{1/p_k^2\}$ and $s_0/\log s_0\ge\max_k\{4/p_k^2\}$. Then
--   $$\mathrm{Myopic}_t(\pi,c,\mathcal G)\le\mathbb E\Big[\frac1{\alpha\,\tilde d_{j,t+1}}+\frac{(\tilde q^*_{j,t}-\hat q^*_j)^2}\alpha\,\Big|\,\mathcal G\Big]\cdot P(\mathcal G).$$
--
--   In this case the policy mimics the fluid solution by a quantile threshold, and the myopic regret is of order $1/s$ plus the squared distance between the fluid and semi-fluid solutions.
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
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 7, (23), p.18; proof p.49

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_IsQuantOpt
import Definitions.Def_DegenNRM_myopicGood

open MeasureTheory

namespace DegenNRM

/-- **Lemma 7: the myopic regret in Case (iii)** (Jiang, Ma & Zhang, arXiv:2210.07996v5,
Lemma 7, (23), p.18).

In Case (iii), `2κ₁ √(log s / s) ≤ q̂*_{j,t} ≤ 1 - 2κ₁ √(log s / s)`, as long as `s ≥ s₀` for a
constant `s₀` with `s₀ log s₀ ≥ (4/κ₁²) max_j {1/p_j²}` and `s₀ / log s₀ ≥ max_j {4/p_j²}`,

`Myopic_t(π, c, G) ≤ E[ 1/(α d̃_{j,t+1}) + (q̃*_{j,t} - q̂*_{j,t})²/α | G ] · P(G)`.

**Formalization Note.** Reading R9 of the mission: the lemma is stated for a fixed remaining
capacity `c ≥ 0`, `s = T - t + 1` periods left and arriving type `j_t = j`; the expectation is
over the `s - 1` later arrivals (a sample path under `pathLaw inst (s - 1)`, whose type counts
are `D = d̃_{t+1}`). `qh = q̂*_t` is an optimal solution of (13) at `(c, s)` (the one Algorithm 2
uses) and `qt D = q̃*_t` an optimal solution of (12) at `(c, d̃_t)`, `d̃_t = D + e_j`, chosen as
in Lemma 4: on `G` it satisfies Lemma 4's bound `‖q̂* − q̃*‖_∞ ≤ κ₁ max_k |d̃_{k,t}/s − p_k|`.
`q^π_{j,t}` is the acceptance probability of the policy (`acceptProb`). `E[X | G]` is
`condMean`, `log` is `Real.log`, and `1/0 = 0` in Lean (on `G` the count `d̃_{j,t+1}` is
positive under the hypotheses). The
printed factor `P(G)` on the right is kept. -/
theorem lemma_7 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (s : ℕ) (j : Fin n)
    (qh : Fin n → ℝ) (hqh : IsFluidOpt inst c (s : ℝ) qh)
    (qt : (Fin n → ℕ) → (Fin n → ℝ))
    (hqt : ∀ D : Fin n → ℕ, ∑ k, D k = s - 1 →
      IsQuantOpt inst c (fun k => (D k : ℝ) + if k = j then 1 else 0) (qt D))
    (hlem4 : ∀ D ∈ goodEvent inst s,
      ‖qh - qt D‖ ≤ kappa1 inst * ‖fun k => ((D k : ℝ) + if k = j then 1 else 0) / s - inst.p k‖)
    (hcase₁ : 2 * kappa1 inst * Real.sqrt (Real.log s / s) ≤ qh j)
    (hcase₂ : qh j ≤ 1 - 2 * kappa1 inst * Real.sqrt (Real.log s / s))
    (s₀ : ℝ) (hs₀₁ : 4 / kappa1 inst ^ 2 * (⨆ k : Fin n, 1 / inst.p k ^ 2) ≤ s₀ * Real.log s₀)
    (hs₀₂ : (⨆ k : Fin n, 4 / inst.p k ^ 2) ≤ s₀ / Real.log s₀) (hs : s₀ ≤ s) :
    myopicGood inst c s j qh qt ≤
      condMean (pathLaw inst (s - 1)) {ω | typeCount ω ∈ goodEvent inst s}
          (fun ω => 1 / (α * typeCount ω j) + (qt (typeCount ω) j - qh j) ^ 2 / α) *
        (pathLaw inst (s - 1)).real {ω | typeCount ω ∈ goodEvent inst s} := by sorry

end DegenNRM
