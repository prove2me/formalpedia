-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_theorem_1
-- name    : DynFairDiv.Uniform.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:51.590013+00:00
-- url     : https://prove2.me/theorems/76533c09-2784-4590-8700-c2a9f7a8bd74
-- title:
--   Theorem 1, p. 950 — if some algorithm has fairness ratio ≥ σ on ψ, the allocations of FFA(ψ,σ) are all feasible
-- statement:
--   Let $\psi$ be a (finite or infinite) control vector of length $n$ and $\sigma \ge 0$. Suppose some feasible arrivals-only allocation sequence $X$ for $\psi$ has fairness ratio at least $\sigma$, i.e. $X^t_k \ge \sigma/t$ for every $1 \le t \le n$ and every user $k < t$. Then every share produced by the frugally fair algorithm with $\psi$ and $\sigma$ is nonnegative, and it never over-allocates:
--   $$S^t(\psi,\sigma) \;=\; \sum_{i=1}^{t} \mathrm{FFA}(\psi,\sigma)^t_i \;\le\; 1 \qquad\text{for all } 1 \le t \le n.$$
--
--   This is the optimality of FFA: among all algorithms that guarantee every present user at least $\sigma/t$, FFA uses the least resource, so the feasibility of FFA decides whether the ratio $\sigma$ is achievable at all.
--
--   **Formalization Note.** An allocation algorithm on $\psi$ is represented by its arrivals-only allocation sequence (the paper's history-independent view, p. 949); the sequence may increase shares freely. The paper's fairness ratios lie in $[0,1]$ (p. 949), so $\sigma \ge 0$ is explicit. This also ensures FFA's output has nonnegative shares, as required by the paper's definition of an allocation (p. 947).
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 950, Theorem 1 (proof pp. 950–951)

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem theorem_1 (ψ : ℕ → ℕ) (n : ℕ∞) (σ : ℝ) (X : ℕ → ℕ → ℝ)
    (hσ : 0 ≤ σ) (hX : AchievesRatio ψ n σ X) :
    ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n →
      (∀ x ∈ ffa ψ σ t, 0 ≤ x) ∧ ffaTotal ψ σ t ≤ 1 := by sorry

end DynFairDiv.Uniform
