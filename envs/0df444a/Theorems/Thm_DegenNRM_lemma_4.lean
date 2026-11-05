-- Prove2me | Theorems.Thm_DegenNRM_lemma_4
-- name    : DegenNRM.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:43.586233+00:00
-- url     : https://prove2.me/theorems/5a803937-1bb2-48f4-8656-15987d29ca0f
-- title:
--   Lemma 4 — every fluid optimum has a semi-fluid optimum within $\kappa_1\max_j|d_j/s-p_j|$, with $\kappa_1$ of (15)
-- statement:
--   Assume Assumption 1. Let $c\ge0$, let $s\ge1$ periods be left, and let $d\in\mathbb N^n$ with $\sum_jd_j=s$ be the type counts of a sample path of these periods. For every optimal solution $\hat q^*$ of the fluid program (13) at $(c,s)$ there is an optimal solution $\tilde q^*$ of the semi-fluid program (12) at $(c,d)$ with
--   $$\|\hat q^*-\tilde q^*\|_\infty\le\kappa_1\cdot\max_{j\in[n]}\Big|\frac{d_j}{s}-p_j\Big|,\qquad \kappa_1=\max_{j\in[n]}\Big\{\frac1{p_j}\Big\}\cdot(m+2n)\cdot\bar a^{\,n}.\tag{14, 15}$$
--
--   The lemma controls how far the algorithm's fluid solution is from the hindsight semi-fluid solution, even when the optima are not unique (degeneracy). It is the reason the policy needs no non-degeneracy assumption.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - reading: F_j⁻¹, the inverse distribution function (not defined in the paper) → F_j⁻¹(q) = inf{r ∈ [l_j, u_j] : F_j((−∞, r]) ≥ q}; reason: the standard generalized inverse, restricted to the reward interval (reading R5)
--   - reading: κ₁ = max_j{1/p_j}·(m + 2n)·āⁿ with ā not defined → ā = max_j (‖a_j‖₂² + 2)^{1/2}; reason: reading R1: the largest column norm of [A; I_n; −I_n], which the proof of Lemma 4 (p.43) bounds; the alternative max_j ‖a_j‖₂ makes Lemma 4 false (m = 1, n = 2, a = (0.01, 0), p = (1/2, 1/2), U[0,1] rewards, c = 0.4, s = 100, d = (40, 60))
--   - reading: 'There exists a constant κ₁ such that for any c ≥ 0 and any optimal solution q̂* to (13) … for any sample path I_t … q̃* denotes one optimal solution to (12). Moreover, κ₁ can be set as (15)' → for every c ≥ 0, s ≥ 1, d ∈ ℕⁿ with Σ_j d_j = s and every optimal q̂* of (13) at (c, s), there exists an optimal q̃* of (12) at (c, d) satisfying (14) with κ₁ of (15); reason: reading R8: the 'Moreover' form with the explicit constant implies the bare existence of κ₁; the ∀ q̂* ∃ q̃* order is the one degeneracy forces (p.9)
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 4, (14)–(15), p.15; proof pp.41–43

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_IsQuantOpt
import Definitions.Def_DegenNRM_kappa1

namespace DegenNRM

/-- **Lemma 4: every fluid optimum has a nearby semi-fluid optimum, with `κ₁` of (15)**
(Jiang, Ma & Zhang, arXiv:2210.07996v5, Lemma 4, (14)–(15), p.15).

Under Assumption 1, let `c ≥ 0`, let `s ≥ 1` periods be left and let `d ∈ ℕⁿ` with
`Σ_j d_j = s` be the type counts of a sample path `I_t` of these periods. For every optimal
solution `q̂*` of (13) at `(c, s)` there is an optimal solution `q̃*` of (12) at `(c, d)` with

`‖q̂* - q̃*‖_∞ ≤ κ₁ · max_{j∈[n]} |d_j/s - p_j|`,

where `κ₁ = max_j {1/p_j} · (m + 2n) · āⁿ` is (15).

**Formalization Note.** The "Moreover" form is stated: the constant is `κ₁` of (15), with
`ā = max_j (‖a_j‖₂² + 2)^{1/2}` (reading R1). For every `q̂*` there exists `q̃*` (reading R8).
The maximum over `j` is the sup norm of `Fin n → ℝ`. -/
theorem lemma_4 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (s : ℕ) (hs : 1 ≤ s) (d : Fin n → ℕ) (hd : ∑ j, d j = s)
    (qh : Fin n → ℝ) (hqh : IsFluidOpt inst c (s : ℝ) qh) :
    ∃ qt : Fin n → ℝ, IsQuantOpt inst c (fun j => (d j : ℝ)) qt ∧
      ‖qh - qt‖ ≤ kappa1 inst * ‖fun j => (d j : ℝ) / s - inst.p j‖ := by sorry

end DegenNRM
