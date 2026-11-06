-- Prove2me | Theorems.Thm_AnchoredEP_lemma_G_2
-- name    : AnchoredEP.lemma_G_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:47:11.825084+00:00
-- url     : https://prove2.me/theorems/ee0a8bfa-9dbb-4bfd-8ab4-5eea67c975b2
-- title:
--   Lemma G.2 — a passing upper trial certifies $\varepsilon$-accuracy
-- statement:
--   Consider Algorithm 3 with order $p\ge2$, $L_p>0$, $\varepsilon>0$ and $v_0\in H(z_0)$, under the standing assumptions ($F$ monotone, $H$ maximal monotone, Problem (1) solvable) and Assumption 5.1, with exact subproblem solutions. At an outer iteration $k$ whose stop test fails, if
--   $$
--   \psi_k(\bar a_k)\le p!\rho\qquad(\rho=1/\sqrt2),
--   $$
--   then $v_{k+1}(\bar a_k)\in H(z_{k+1}(\bar a_k))$, $\|F(z_{k+1}(\bar a_k))+v_{k+1}(\bar a_k)\|\le\varepsilon$, and hence $\mathrm{res}^{\tan}(z_{k+1}(\bar a_k))\le\varepsilon$.
--
--   This justifies returning the upper trial point when the merit function passes at $\bar a_k$.
--
--   Differences from the source:
--   - encoding: the (p−1)th derivative of F exists and is L_p-Lipschitz (Assumption 5.1) → Assumption51 p L F = ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv (p−1) F z − iteratedFDeriv (p−1) F z′‖ ≤ L‖z − z′‖; reason: the existence of D^{p−1}F is presupposed by the source; a Lipschitz (p−1)th derivative is continuous, so the same operators qualify
--   - encoding: outer iteration k of Algorithm 3 (exact subproblem solutions) → a state s with tensorRun F p L ε sol z0 v0 k = .running s, for every solver sol with IsSubSolver; reason: Algorithm 3 as a deterministic run with its subproblem oracle as a parameter; the solution of (87) is unique, so every admissible solver gives the source's run
--   - encoding: res^tan(z) = inf over H(z) of ‖F(z)+v‖ (+∞ on an empty set) → tangentResidual = real sInf of the image (0 on an empty set); reason: the same value whenever H(z) is nonempty, which the stated membership guarantees
--   - generalization: res^tan(z_{k+1}(ā_k)) ≤ ε → additionally v_{k+1}(ā_k) ∈ H(z_{k+1}(ā_k)) and ‖F(z_{k+1}(ā_k)) + v_{k+1}(ā_k)‖ ≤ ε; reason: the proof establishes exactly this certificate; it implies the source's conclusion
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Lemma G.2, p.38

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_IsSolution
import Definitions.Def_AnchoredEP_tangentResidual
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_IsSubSolver
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialZ
import Definitions.Def_AnchoredEP_trialV
import Definitions.Def_AnchoredEP_abar
import Definitions.Def_AnchoredEP_upperPasses
import Definitions.Def_AnchoredEP_RunState
import Definitions.Def_AnchoredEP_tensorRun

open ThreeOpSplitting.Convergence

namespace AnchoredEP

/-- **Lemma G.2 (the upper trial certifies `ε`-accuracy).** Jiang–Yoon, arXiv:2609.30212,
Lemma G.2, p.38: "If `ψ_k(ā_k) ≤ p!ρ`, then `res^tan(z_{k+1}(ā_k)) ≤ ε`."

Setting: Algorithm 3 with order `p ≥ 2`, `L_p > 0`, `ε > 0`, `v₀ ∈ H(z₀)`, under the standing
assumptions (`F` monotone, `H` maximal monotone, Problem (1) solvable) and Assumption 5.1, with
any exact subproblem solver `sol`. At any outer iteration `k` the run reaches whose stop test
fails (so the line search is applied), if the upper trial passes then the returned pair
`(z_{k+1}(ā_k), v_{k+1}(ā_k))` satisfies `v_{k+1}(ā_k) ∈ H(z_{k+1}(ā_k))`,
`‖F(z_{k+1}(ā_k)) + v_{k+1}(ā_k)‖ ≤ ε`, and hence `res^tan(z_{k+1}(ā_k)) ≤ ε`.

**Formalization Note.** `upperPasses` is `ψ_k(ā_k) ≤ p!ρ` with `ρ = 1/√2`. The membership and the
norm bound are stated besides `res^tan ≤ ε` because the real `sInf` in `tangentResidual` would be
`0` on an empty set. -/
theorem lemma_G_2 {d : ℕ} (p : ℕ) (hp : 2 ≤ p) (L ε : ℝ)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin d)))))
    (hH : IsMaximalMonotone H) (hsolv : ∃ zstar, IsSolution F H zstar)
    (hA : Assumption51 p L F) (hL : 0 < L) (hε : 0 < ε)
    (z0 v0 : EuclideanSpace ℝ (Fin d)) (hv0 : v0 ∈ H z0)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsol : IsSubSolver F H p L sol)
    (k : ℕ) (s : IterState d) (hk : tensorRun F p L ε sol z0 v0 k = .running s)
    (hstop : ε < ‖F s.z + s.v‖) (hup : upperPasses F p L ε sol z0 s) :
    trialV F p L sol z0 s (abar F p L ε s) ∈ H (trialZ F sol z0 s (abar F p L ε s)) ∧
      ‖F (trialZ F sol z0 s (abar F p L ε s)) + trialV F p L sol z0 s (abar F p L ε s)‖ ≤ ε ∧
      tangentResidual F H (trialZ F sol z0 s (abar F p L ε s)) ≤ ε := by sorry

end AnchoredEP
