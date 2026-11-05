-- Prove2me | Theorems.Thm_DegenNRM_lemma_2
-- name    : DegenNRM.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:39.189445+00:00
-- url     : https://prove2.me/theorems/798c2ab2-941b-4a73-9326-0631614646fe
-- title:
--   Lemma 2 — the semi-fluid relaxation upper-bounds the prophet: $\mathbb E[\bar V^{\mathrm{Semi}}_C(\tilde d_1)]\ge\mathbb E[V^{\mathrm{off}}(I)]$
-- statement:
--   Assume Assumption 1, let $C\ge0$ be the initial capacities and $T$ the number of periods. Then
--   $$\mathbb E_I\big[\bar V^{\mathrm{Semi}}_C(\tilde d_1)\big]\ge\mathbb E_I\big[V^{\mathrm{off}}(I)\big],$$
--   where $\tilde d_1=(\tilde d_{1,1},\dots,\tilde d_{n,1})$ are the type counts of the sample path $I$. Both random variables are integrable.
--
--   With $\bar V=\bar V^{\mathrm{Semi}}$ this is hypothesis (6) of Lemma 1.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - encoding: (9): max over x_j(r) ∈ [0,1] for r ∈ [l_j, u_j] → the supremum (sSup) over measurable x_j : ℝ → [0,1]; reason: F_j lives on [l_j, u_j], so values outside do not matter; measurability makes the expectations meaningful; Lemma 3 and (12) show the supremum is attained
--   - generalization: E_I[V̄^Semi_C(d̃_1)] ≥ E_I[V^off(I)] → the inequality together with the integrability of both random variables; reason: the paper takes the expectations for granted; dropping the two integrability conjuncts gives the printed statement
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 2, p.13

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_arrivalLaw
import Definitions.Def_DegenNRM_offlineValue
import Definitions.Def_DegenNRM_semiValue

open MeasureTheory

namespace DegenNRM

/-- **Lemma 2: the semi-fluid relaxation upper-bounds the prophet** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, Lemma 2, p.13).

Under Assumption 1, for initial capacities `C ≥ 0` and `T` periods,
`E_I[V̄^Semi_C(d̃_1)] ≥ E_I[V^off(I)]`, where `d̃_1 = (d̃_{1,1}, …, d̃_{n,1})` are the type counts
of the sample path `I`.

**Formalization Note.** Both integrands are asserted integrable as well, so the inequality is
between the expectations the paper writes. -/
theorem lemma_2 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α)
    (C : Fin m → ℝ) (hC : 0 ≤ C) (T : ℕ) :
    Integrable (offlineValue inst C) (pathLaw inst T) ∧
      Integrable (fun ω => semiValue inst C (fun j => (typeCount ω j : ℝ))) (pathLaw inst T) ∧
      ∫ ω, offlineValue inst C ω ∂(pathLaw inst T) ≤
        ∫ ω, semiValue inst C (fun j => (typeCount ω j : ℝ)) ∂(pathLaw inst T) := by sorry

end DegenNRM
