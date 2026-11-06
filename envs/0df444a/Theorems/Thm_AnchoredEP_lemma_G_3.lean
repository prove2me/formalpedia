-- Prove2me | Theorems.Thm_AnchoredEP_lemma_G_3
-- name    : AnchoredEP.lemma_G_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:17.900323+00:00
-- url     : https://prove2.me/theorems/69aecd51-1577-42f1-b6a4-4a993da64ce9
-- title:
--   Lemma G.3 — regularity of the tensor merit function
-- statement:
--   For every order $p\ge2$ there is a constant $C_p>0$, depending only on $p$, such that for every instance of Algorithm 3 ($L_p>0$, $\varepsilon>0$, $v_0\in H(z_0)$, $M_p=(p+1)L_p$, standing assumptions with any solution $z^\ast$, Assumption 5.1, exact subproblem solutions), at every outer iteration $k$ before termination:
--
--   1. $\psi_k$ is continuous on $[0,\bar a_k]$;
--   2. $\displaystyle \mathrm{Lip}(\psi_k;[0,\bar a_k])\le C_pM_p\|z_0-z^\ast\|^{p-1}\big(1+M_p\|z_0-z^\ast\|^{p-1}\bar a_k\big)^{2p-2}$;
--   3. if the bisection phase is entered,
--   $$
--   M_p\|z_0-z^\ast\|^{p-1}\bar a_k\le C_p\max\Big\{\frac{L_p\|z_0-z^\ast\|^p}{\varepsilon},\ \Big(\frac{L_p\|z_0-z^\ast\|^p}{\varepsilon}\Big)^{(p-1)/p}\Big\} .
--   $$
--   Since each bisection halves the interval, these bounds limit the number of bisection trials to a logarithm of $1+L_p\|z_0-z^\ast\|^p/\varepsilon$.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: outer iteration before termination (the earlier iterations returned accepted steps) → tensorRun … k = .running s, stop test failing at s, and every earlier line search returns (hypothesis on LineSearchReturnsWithin); reason: the earlier-search hypothesis only excludes the placeholder branch of stepSize, which never occurs (Theorem 5.1 proves the search always returns)
--   - encoding: a constant C_p > 0 depending only on p → ∃ C > 0 quantified after p and before the dimension and all data; reason: the source's O_p / C_p convention
--   - encoding: Lip(ψ_k; [0, ā_k]) ≤ K → ∀ a b ∈ [0, ā_k], |ψ_k(a) − ψ_k(b)| ≤ K|a − b|; reason: definition of the Lipschitz modulus as a supremum of difference quotients
--   - encoding: the bisection phase is entered → ¬ upperPasses (ψ_k(ā_k) > p!ρ); reason: the bisection starts exactly when the upper trial fails
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma G.3, p.39, Eqs. (97)–(98)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IsSubSolver
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_psi
import Definitions.Def_AnchoredEP_abar
import Definitions.Def_AnchoredEP_upperPasses
import Definitions.Def_AnchoredEP_LineSearchReturnsWithin
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_tensorRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Lemma G.3 (regularity of the tensor merit function).** Jiang–Yoon, arXiv:2609.30212,
Lemma G.3, Eqs. (97)–(98), p.39: "There is a constant `C_p > 0` depending only on `p` such that, at
every outer iteration before termination, `ψ_k` is continuous on `[0, ā_k]` and
`Lip(ψ_k; [0, ā_k]) ≤ C_p M_p‖z₀ − z∗‖^{p−1} (1 + M_p‖z₀ − z∗‖^{p−1} ā_k)^{2p−2}`. (97) Moreover, if
the bisection phase is entered, then
`M_p‖z₀ − z∗‖^{p−1} ā_k ≤ C_p max{ L_p‖z₀ − z∗‖^p/ε , (L_p‖z₀ − z∗‖^p/ε)^{(p−1)/p} }`. (98)"

For each order `p ≥ 2` there is one `C_p > 0` such that, for every dimension and every instance
of Algorithm 3 (`L_p > 0`, `ε > 0`, `v₀ ∈ H(z₀)`, `M_p = (p + 1)L_p`, standing assumptions with any
solution `z∗`, Assumption 5.1, any exact subproblem solver), at every outer iteration `k` the run
reaches before termination, all three clauses hold: continuity, (97), and (98) when the upper
trial fails.

**Formalization Note.** `ψ_k` is `psi` (with `ψ_k(0) = 0`, Eq. (89)); "`Lip(ψ_k; [0, ā_k]) ≤ K`" is
`∀ a b ∈ [0, ā_k], |ψ_k(a) − ψ_k(b)| ≤ K |a − b|`. "The bisection phase is entered" is
`¬ upperPasses`. The constant is quantified before the dimension and the data. "Before
termination" is `tensorRun … k = .running s`, the stop test failing at `s`, and every earlier
line search having returned (`hacc`). The power `(p−1)/p` is a real power. -/
theorem lemma_G_3 (p : ℕ) (hp : 2 ≤ p) :
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
      ContinuousOn (psi F p L sol z0 s) (Set.Icc 0 (abar F p L ε s)) ∧
      (∀ a ∈ Set.Icc 0 (abar F p L ε s), ∀ b ∈ Set.Icc 0 (abar F p L ε s),
        |psi F p L sol z0 s a - psi F p L sol z0 s b| ≤
          C * (((p : ℝ) + 1) * L) * ‖z0 - zstar‖ ^ (p - 1) *
            (1 + ((p : ℝ) + 1) * L * ‖z0 - zstar‖ ^ (p - 1) * abar F p L ε s) ^ (2 * p - 2) *
            |a - b|) ∧
      (¬ upperPasses F p L ε sol z0 s →
        ((p : ℝ) + 1) * L * ‖z0 - zstar‖ ^ (p - 1) * abar F p L ε s ≤
          C * max (L * ‖z0 - zstar‖ ^ p / ε)
            ((L * ‖z0 - zstar‖ ^ p / ε) ^ (((p : ℝ) - 1) / (p : ℝ)))) := by sorry

end AnchoredEP
