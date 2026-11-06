-- Prove2me | Theorems.Thm_AnchoredEP_lemma_H_1
-- name    : AnchoredEP.lemma_H_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:47:21.078386+00:00
-- url     : https://prove2.me/theorems/f963a10f-446d-4895-bcbd-1e94ca096994
-- title:
--   Lemma H.1 — tensor merit sensitivity
-- statement:
--   Consider Algorithm 3 with order $p\ge2$, $L_p>0$, $\varepsilon>0$, $v_0\in H(z_0)$ and $M_p=(p+1)L_p$, under the standing assumptions and Assumption 5.1, with exact subproblem solutions, at an outer iteration $k$ whose stop test fails. Suppose the trial displacement $d_k$ is Lipschitz continuous on $[0,\bar a_k]$. Then $\psi_k$ is Lipschitz continuous on $[0,\bar a_k]$ with
--   $$
--   \mathrm{Lip}(\psi_k;[0,\bar a_k])\le M_p\Big(\sup_{0\le a\le\bar a_k}\|d_k(a)\|\Big)^{p-1}+(p-1)M_p\bar a_k\Big(\sup_{0\le a\le\bar a_k}\|d_k(a)\|\Big)^{p-2}\mathrm{Lip}(d_k;[0,\bar a_k]) .
--   $$
--   It reduces the regularity of the merit function to bounds on the trial displacement.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: Lip(ψ_k) ≤ M_p (sup‖d_k‖)^{p−1} + (p−1)M_p ā_k (sup‖d_k‖)^{p−2} Lip(d_k) → for all S ≥ ‖d_k‖ and D with ‖d_k(a) − d_k(b)‖ ≤ D|a − b| on [0, ā_k]: |ψ_k(a) − ψ_k(b)| ≤ (M_p S^{p−1} + (p−1)M_p ā_k S^{p−2} D)|a − b|; reason: the source's bound is the case S = sup, D = Lip; the right side increases in S, D ≥ 0, so the two forms are equivalent
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma H.1, p.40, Eq. (100)

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

/-- **Lemma H.1 (tensor merit sensitivity).** Jiang–Yoon, arXiv:2609.30212, Lemma H.1, Eq. (100),
p.40: "Suppose that `d_k` is Lipschitz continuous on `[0, ā_k]`. Then `ψ_k` is Lipschitz continuous
on the same interval, with
`Lip(ψ_k; [0, ā_k]) ≤ M_p (sup_{0≤a≤ā_k} ‖d_k(a)‖)^{p−1} + (p−1)M_p ā_k (sup_{0≤a≤ā_k} ‖d_k(a)‖)^{p−2} Lip(d_k; [0, ā_k])`."

Setting: Algorithm 3 with order `p ≥ 2`, `L_p > 0`, `ε > 0`, `v₀ ∈ H(z₀)`, `M_p = (p + 1)L_p`,
under the standing assumptions and Assumption 5.1, with any exact subproblem solver; `k` is an
outer iteration the run reaches whose stop test fails. If `‖d_k(a)‖ ≤ S` on `[0, ā_k]` and `d_k`
is `D`-Lipschitz there, then `ψ_k` is
`(M_p S^{p−1} + (p − 1)M_p ā_k S^{p−2} D)`-Lipschitz on `[0, ā_k]`.

**Formalization Note.** `d_k` is `trialDisp` (with `d_k(0) = 0`, Eq. (99)) and `ψ_k` is `psi`.
"`Lip(f; I) ≤ K`" is written `∀ a b ∈ I, ‖f a − f b‖ ≤ K |a − b|`. The supremum and the Lipschitz
modulus of `d_k` are replaced by arbitrary bounds `S` and `D`: the source's statement is the case
`S = sup ‖d_k‖`, `D = Lip(d_k)`, and since the right-hand side increases in `S, D ≥ 0` the two
forms are equivalent. For `p = 2`, `S^{p−2} = S⁰ = 1`. -/
theorem lemma_H_1 {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (L ε : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hH : IsMaximalMonotone H) (hsolv : ∃ zstar, IsSolution F H zstar)
    (hA : Assumption51 p L F) (hL : 0 < L) (hε : 0 < ε)
    (z0 v0 : EuclideanSpace ℝ (Fin d)) (hv0 : v0 ∈ H z0)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsol : IsSubSolver F H p L sol)
    (k : ℕ) (s : IterState d) (hk : tensorRun F p L ε sol z0 v0 k = .running s)
    (hstop : ε < ‖F s.z + s.v‖)
    (S D : ℝ)
    (hS : ∀ a ∈ Set.Icc 0 (abar F p L ε s), ‖trialDisp F sol z0 s a‖ ≤ S)
    (hD : ∀ a ∈ Set.Icc 0 (abar F p L ε s), ∀ b ∈ Set.Icc 0 (abar F p L ε s),
      ‖trialDisp F sol z0 s a - trialDisp F sol z0 s b‖ ≤ D * |a - b|) :
    ∀ a ∈ Set.Icc 0 (abar F p L ε s), ∀ b ∈ Set.Icc 0 (abar F p L ε s),
      |psi F p L sol z0 s a - psi F p L sol z0 s b| ≤
        (((p : ℝ) + 1) * L * S ^ (p - 1) +
          ((p : ℝ) - 1) * (((p : ℝ) + 1) * L) * abar F p L ε s * S ^ (p - 2) * D) * |a - b| := by sorry

end AnchoredEP
