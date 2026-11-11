-- Prove2me | Theorems.Thm_CellProbeTree_Matching_lemma_A_2
-- name    : CellProbeTree.Matching.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:32.557652+00:00
-- url     : https://prove2.me/theorems/3ab1fe61-3b0c-4ed8-8aa7-59ad91bb92e9
-- title:
--   Lemma A.2 — uniform local bound $a_{v,s} \le Cv^{-2}$ and truncated moments of the conditioned critical Catalan vector
-- statement:
--   Let $p_s = C_s/(2\cdot 4^s)$ be the critical Catalan law, $T_v$ the sum of $v$ independent copies, and $a_{v,s} = \Pr[T_v = s]$. There is an absolute constant $C$ such that
--   $$\sup_{s \ge 0} a_{v,s} \le C v^{-2} \qquad (v \ge 1).$$
--   Moreover, for every fixed compact positive interval $[c_-, c_+]$ there is $C'$, depending only on the interval, such that whenever $v \ge 2$ and $s/v^2 \in [c_-, c_+]$, every coordinate $Z_i$ of the vector conditioned on $T_v = s$ satisfies, for every $z \ge 0$ and every $A \ge 1$,
--   $$\Pr[Z_i = z \mid T_v = s] \le C' p_z, \qquad \mathbb E\big[\min(Z_i + 1, A) \,\big|\, T_v = s\big] \le C'\sqrt A .$$
--
--   Differences from the source:
--   - encoding: the conditional probability and conditional expectation → finite sums over the tuples summing to $s$ divided by $a_{v,s}$ (`critCondProb`, `critCondTruncMean`), coordinates 0-based; $v^{-2}$ → `((v : ℝ) ^ 2)⁻¹`; the compact positive interval → $[c_-, c_+]$ with $0 < c_- \le c_+$; reason: Lean representation of the conditioned law (71).
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 42, Appendix A.4, Lemma A.2

import Mathlib
import Definitions.Def_CellProbeTree_Matching_CriticalCatalan

namespace CellProbeTree.Matching

/-- Lemma A.2: for the critical Catalan law `p_s = C_s/(2·4^s)` and `a_{v,s} = Pr[T_v = s]`,
there is an absolute `C` with `sup_s a_{v,s} ≤ C v^{−2}` for all `v ≥ 1`; and for every fixed
compact interval `[c₋, c₊] ⊂ (0, ∞)` there is `C'` such that, whenever `v ≥ 2` and
`s/v² ∈ [c₋, c₊]`, every coordinate of the vector conditioned on `T_v = s` satisfies
`Pr[Z_i = z | T_v = s] ≤ C' p_z` and `E[min(Z_i + 1, A) | T_v = s] ≤ C' √A` for every `A ≥ 1`. -/
theorem lemma_A_2 :
    (∃ C : ℝ, ∀ v : ℕ, 1 ≤ v → ∀ s : ℕ, critA v s ≤ C * ((v : ℝ) ^ 2)⁻¹) ∧
    (∀ cm cp : ℝ, 0 < cm → cm ≤ cp →
      ∃ C' : ℝ, ∀ v s : ℕ, 2 ≤ v → cm ≤ (s : ℝ) / (v : ℝ) ^ 2 → (s : ℝ) / (v : ℝ) ^ 2 ≤ cp →
        ∀ i : Fin v,
          (∀ z : ℕ, critCondProb v s i z ≤ C' * critP z) ∧
          (∀ A : ℝ, 1 ≤ A → critCondTruncMean v s i A ≤ C' * Real.sqrt A)) := by sorry

end CellProbeTree.Matching
