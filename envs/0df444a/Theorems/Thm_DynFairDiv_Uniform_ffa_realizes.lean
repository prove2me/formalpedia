-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_ffa_realizes
-- name    : DynFairDiv.Uniform.ffa_realizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:54.753038+00:00
-- url     : https://prove2.me/theorems/babc99af-8c1f-43b8-b9cd-0a9296903af5
-- title:
--   §3, p. 949 — whenever FFA(ψ,σ) stays feasible, its allocations form a feasible allocation sequence with fairness ratio at least σ
-- statement:
--   Let $\psi$ be a control vector of length $n \in \{0,1,2,\dots\}\cup\{\infty\}$ and let $\sigma \ge 0$. Suppose that the frugally fair algorithm $\mathrm{FFA}(\psi,\sigma)$ never allocates more than the whole resource:
--   $$S^t \le 1 \qquad \text{for all } 1 \le t \le n,$$
--   where $S^t$ is the total resource FFA allocates when $t$ users are present. Then FFA's shares can be assigned to users by arrival order to form a feasible arrivals-only allocation sequence $X$ for $\psi$ (shares nonnegative, totals at most one, at most $\psi[t]$ existing users disrupted at the $t$-th arrival) whose fairness ratio is at least $\sigma$: $X^t_k \ge \sigma/t$ for all $1 \le t \le n$ and all $k < t$. At each time, the list of $X$'s shares is a permutation of FFA's list.
--
--   This is the sense in which FFA "generates allocations": invoking FFA with $\psi$ and a feasible ratio $\sigma$ yields an allocation algorithm with fairness ratio $\sigma$, on the fly and for infinite control vectors as well.
--
--   **Formalization Note.** The sequence $X$ follows FFA's shares with users labelled by arrival order. The hypothesis $\sigma \ge 0$ is added: for $\sigma < 0$ FFA's shares are negative and no feasible allocation copies them; the paper only runs FFA with fairness ratios, which lie in $[0,1]$. Arrivals only, as in §§3–5 of the paper.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 949, §3 ('if we know the optimal fairness ratio for ψ … we can invoke FFA with ψ and FAIRNESS(ψ) and generate optimal allocations'); p. 950 after Algorithm 1; p. 952, §5.1

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem ffa_realizes (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (hσ : 0 ≤ σ)
    (hfeas : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n → ffaTotal ψ σ t ≤ 1) :
    ∃ X, AchievesRatio ψ n σ X ∧
      ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
        (List.ofFn (fun k : Fin t => X t k.val)).Perm (ffa ψ σ t) := by sorry

end DynFairDiv.Uniform
