-- Prove2me | Theorems.Thm_FasterSFM_lemma_13
-- name    : FasterSFM.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:49.45017+00:00
-- url     : https://prove2.me/theorems/35e2dae8-8747-442c-be87-e3e736ba36b2
-- title:
--   Lemma 13 — inserted and cutting-plane row bounds: $k\le k_n$, $Q_n<Kp_n^2$, $\chi_n<1$
-- statement:
--   Let $P$ be an admissible body with $k$ inserted rows and $S$ a subspace (orthonormal basis $J$), and suppose the potential satisfies $\Phi(S,P)\ge\frac n2\log2+k\gamma/8$, which is what $k$ wide steps from the initial cube give, contractions never lowering $\Phi$. Then
--
--   $$k\le k_n,\qquad M=2n+k\le M^*:=2n+k_n. \tag{14}$$
--
--   Moreover $k_n=O(n\log(n+2))$, i.e. $k_n\le Cn\log(n+2)$ for an absolute $C$ and all $n\ge1$, and for every $n$
--
--   $$Q_n=k_n+n<Kp_n^2,\qquad \chi_n=Q_n\delta<1,$$
--
--   with the explicit forms of the proof: $k_n=2^{31}n[40\log K+40\log p_n+\log(1+2^{29})]$, $k_n<2^{43}p_n^2$, $Q_n<2^{44}p_n^2$ and $\chi_n\le K^{-19}p_n^{-18}$.
--
--   These bounds control the number of rows, the number of oracle calls (Theorem 14) and all size-dependent constants of the analysis.
--
--   Differences from the source:
--   - reading: "consider any point in the algorithm" with k inserted rows → an admissible body with k inserted rows and a subspace S with Φ(S, P) ≥ (n/2) log 2 + kγ/8; reason: reading R7: the potential facts the algorithm supplies (Lemma 11; contractions never decrease Φ; initial value (n/2) log 2, p.25)
--   - encoding: k_n = O(n log(n + 2)) → ∃ C, ∀ n ≥ 1, k_n ≤ C n log(n + 2); reason: reading R1: explicit constant
--   - generalization: the three bounds of the statement → also the explicit forms of the proof (pp.25–26): the formula for k_n, k_n < 2⁴³p_n², Q_n < 2⁴⁴p_n², χ_n ≤ K⁻¹⁹p_n⁻¹⁸; reason: they imply the stated bounds and are used by Lemma 16
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 13, eq. (14), p.25; explicit bounds pp.25–26

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier

namespace FasterSFM

open Classical Matrix

/-- **Lemma 13** (Inserted and cutting plane row bounds), p.25.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 13, eq. (14), p.25, with the explicit bounds of its proof,
pp.25–26.

"Consider any point in the algorithm and let k be the number of rows inserted so far. We have
k ≤ k_n, M = 2n + k ≤ M* := 2n + k_n. (14) Moreover, k_n = O(n log(n + 2)), Q_n = k_n + n < K p_n²,
χ_n = Q_n δ < 1."

**Formalization Note.**
* Reading R7: "at any point in the algorithm" is replaced by the fact the algorithm supplies at that
  point: the potential has risen by at least `γ/8` per inserted row from its initial value
  `(n/2) log 2` (Lemma 11; contractions never lower it, p.25), i.e.
  `Φ(S, P) ≥ (n/2) log 2 + kγ/8`, for an admissible body `P` with `k` inserted rows and a subspace
  `S` (column space of `J`, `JᵀJ = I`). The conclusion is `k ≤ k_n` and `M = 2n + k ≤ M*`.
* `k_n = O(n log(n+2))` is: there is `C` with `k_n ≤ C n log(n + 2)` for every `n ≥ 1`.
* The explicit forms of the proof (pp.25–26) are added as conjuncts:
  `k_n = 2³¹ n [40 log K + 40 log p_n + log(1 + 2²⁹)]`, `k_n < 2⁴³ p_n²`, `Q_n < 2⁴⁴ p_n²`,
  `χ_n ≤ K⁻¹⁹ p_n⁻¹⁸`. -/
theorem lemma_13 :
    (∀ {n N : ℕ} (P : Body n), P.Admissible →
      ∀ (J : Matrix (Fin n) (Fin N) ℝ), Jᵀ * J = 1 →
      (n : ℝ) / 2 * Real.log 2 + (P.k : ℝ) * gam / 8 ≤ P.Phi (colSpace J) →
      (P.k : ℝ) ≤ kn n ∧ (P.M : ℝ) ≤ Mstar n) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → kn n ≤ C * n * Real.log ((n : ℝ) + 2)) ∧
    (∀ n : ℕ,
      Qn n < Kc * pn n ^ 2 ∧ chi n < 1 ∧
      kn n = 2 ^ 31 * n * (40 * Real.log Kc + 40 * Real.log (pn n) + Real.log (1 + 2 ^ 29)) ∧
      kn n < 2 ^ 43 * pn n ^ 2 ∧ Qn n < 2 ^ 44 * pn n ^ 2 ∧
      chi n ≤ Kc ^ (-19 : ℤ) * pn n ^ (-18 : ℤ)) := by sorry

end FasterSFM
