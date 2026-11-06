-- Prove2me | Theorems.Thm_AnchoredEP_lemma_H_2
-- name    : AnchoredEP.lemma_H_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:47:02.93339+00:00
-- url     : https://prove2.me/theorems/997033d4-c091-4cc3-ae31-11d7bc3f74f2
-- title:
--   Lemma H.2 — trial displacement bound
-- statement:
--   For every order $p\ge2$ there is a constant $C_p>0$, depending only on $p$, such that for every instance of Algorithm 3 ($L_p>0$, $\varepsilon>0$, $v_0\in H(z_0)$, $M_p=(p+1)L_p$, standing assumptions with any solution $z^\ast$, Assumption 5.1, exact subproblem solutions), at every outer iteration $k$ reached before termination and for every $0<a\le\bar a_k$,
--   $$
--   \|d_k(a)\|\le C_p\big(1+M_p\|z_0-z^\ast\|^{p-1}\bar a_k\big)\,\|z_0-z^\ast\| .
--   $$
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: outer iteration before termination (the earlier iterations returned accepted steps) → tensorRun … k = .running s, stop test failing at s, and every earlier line search returns (hypothesis on LineSearchReturnsWithin); reason: the earlier-search hypothesis only excludes the placeholder branch of stepSize, which never occurs (Theorem 5.1 proves the search always returns)
--   - encoding: a constant C_p > 0 depending only on p → ∃ C > 0 quantified after p and before the dimension and all data; reason: the source's O_p / C_p convention
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma H.2, p.41, Eq. (101)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IsSubSolver
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialDisp
import Definitions.Def_AnchoredEP_psi
import Definitions.Def_AnchoredEP_abar
import Definitions.Def_AnchoredEP_LineSearchReturnsWithin
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_tensorRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Lemma H.2 (trial displacement).** Jiang–Yoon, arXiv:2609.30212, Lemma H.2, Eq. (101), p.41:
"For every `k ≥ 0` and `0 < a ≤ ā_k`, `‖d_k(a)‖ ≤ C_p (1 + M_p‖z₀ − z∗‖^{p−1} ā_k) ‖z₀ − z∗‖`,
where `C_p > 0` depends only on `p`."

For each order `p ≥ 2` there is one `C_p > 0` such that, for every dimension and every instance
of Algorithm 3 (`L_p > 0`, `ε > 0`, `v₀ ∈ H(z₀)`, `M_p = (p + 1)L_p`, standing assumptions with any
solution `z∗`, Assumption 5.1, any exact subproblem solver), at every outer iteration `k` the run
reaches before termination (stop test failing) the bound holds for `0 < a ≤ ā_k`.

**Formalization Note.** `d_k` is `trialDisp` (Eq. (99)). The constant is quantified before the
dimension and the data. "Before termination" is `tensorRun … k = .running s`, the stop test
failing at `s`, and every earlier line search having returned (`hacc`, the source's accepted
steps; it only excludes the placeholder branch of `stepSize`). -/
theorem lemma_H_2 (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (L ε : ℝ)
      (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
      (z0 v0 zstar : EuclideanSpace ℝ (Fin d))
      (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))) →
      IsMaximalMonotone H → IsSolution F H zstar →
      Assumption51 p L F → 0 < L → 0 < ε → v0 ∈ H z0 → IsSubSolver F H p L sol →
      ∀ (k : ℕ) (s : IterState d), tensorRun F p L ε sol z0 v0 k = .running s →
      ε < ‖F s.z + s.v‖ →
      (∀ i < k, ∀ s' : IterState d, tensorRun F p L ε sol z0 v0 i = .running s' →
        ε < ‖F s'.z + s'.v‖ → ∃ n : ℕ, LineSearchReturnsWithin F p L ε sol z0 s' n) →
      ∀ a : ℝ, 0 < a → a ≤ abar F p L ε s →
        ‖trialDisp F sol z0 s a‖ ≤
          C * (1 + ((p : ℝ) + 1) * L * ‖z0 - zstar‖ ^ (p - 1) * abar F p L ε s) * ‖z0 - zstar‖ := by sorry

end AnchoredEP
