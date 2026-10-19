-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_proposition_2
-- name    : DynFairDiv.Uniform.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:54.466866+00:00
-- url     : https://prove2.me/theorems/8a3725ae-491c-44c7-9cd8-2e337b3ad2c7
-- title:
--   Proposition 2, p. 952 — the fairness ratio of a control vector is at most that of any of its prefixes
-- statement:
--   Let $\psi$ be a control vector of length $n \in \{1,2,\dots\}\cup\{\infty\}$ and let $\psi'$ be a prefix of $\psi$ of length $1 \le n' \le n$, i.e. $\psi'[t] = \psi[t]$ for $1 \le t \le n'$. Then
--   $$\mathrm{FAIRNESS}(\psi) \;\le\; \mathrm{FAIRNESS}(\psi'),$$
--   where $\mathrm{FAIRNESS}(\psi)$ is the supremum of the fairness ratios of all feasible arrivals-only allocation sequences for $\psi$.
--
--   Lengthening a control vector can only lower its optimal fairness ratio; for $d$-uniform vectors this is what makes the infinite vector the worst case.
--
--   **Formalization Note.** The hypothesis $n' \ge 1$ is added: every control vector has an entry $\psi[1]$ (Definition 2), and for an empty vector the supremum over all real numbers is a junk value in Lean. Values of $\psi$ outside $[1, n]$ play no role.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 952, Proposition 2 (proof p. 958, Appendix E.1)

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem proposition_2 (ψ ψ' : ℕ → ℕ) (n n' : ℕ∞) (hn' : 1 ≤ n') (hle : n' ≤ n)
    (hpre : ∀ t : ℕ, 1 ≤ t → (t : ℕ∞) ≤ n' → ψ' t = ψ t) :
    fairnessRatio ψ n ≤ fairnessRatio ψ' n' := by sorry

end DynFairDiv.Uniform
