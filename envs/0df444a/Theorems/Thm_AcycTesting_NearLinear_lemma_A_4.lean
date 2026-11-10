-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_A_4
-- name    : AcycTesting.NearLinear.lemma_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:46.20839+00:00
-- url     : https://prove2.me/theorems/d50ff087-959c-4289-8b86-fedf68ca926f
-- title:
--   Lemma A.4 — lower tail of balanced cuts: Pr[cut(V₁) ≤ 4N] ≤ e^{−N}
-- statement:
--   Let $V_1\subseteq[N]$ have size $N/2$, and let $\mathrm{cut}(V_1)$ be the number of occurrences $v\xrightarrow{a}\pi_a(v)$ of $\Gamma(\Pi)$ with $v\in V_1$ and $\pi_a(v)\notin V_1$, for 32 independent uniform permutations $\pi_1,\dots,\pi_{32}$ of $[N]$ (no girth conditioning). Then
--   $$\Pr[\mathrm{cut}(V_1)\le 4N]\ \le\ e^{-N}.$$
--   The mean of $\mathrm{cut}(V_1)$ is $8N$; the exponentially small lower tail survives a union bound over all balanced sets and the girth conditioning (Proposition 3.3).
--
--   Differences from the source:
--   - encoding: |V1| = N/2 → 2·|V₁| = N; reason: the same condition without division
--   - encoding: Pr / E over independent uniform permutations π1, …, π32 → probU / expU: uniform on PermTuple N = Fin 32 → Equiv.Perm (Fin N); reason: the product of independent uniform laws is uniform on tuples
--   - encoding: [N], colours [32] → Fin N, Fin 32; reason: Lean convention
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 39 (PDF 42), Lemma A.4

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_Digraphs
import Definitions.Def_AcycTesting_NearLinear_PermCores

namespace AcycTesting.NearLinear

/-- Lemma A.4 (lower tail of balanced cuts): for `|V₁| = N/2` and uniform independent
permutations, `Pr[cut(V₁) ≤ 4N] ≤ e^{-N}`. -/
theorem lemma_A_4 (N : ℕ) (V₁ : Finset (Fin N)) (hV : 2 * V₁.card = N) :
    probU (fun πs : PermTuple N => cut πs V₁ ≤ 4 * N) ≤ Real.exp (-(N : ℝ)) := by sorry

end AcycTesting.NearLinear
