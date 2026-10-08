-- Prove2me | Theorems.Thm_Disjunctive_LiftProject_mip_cut_lifting_v2
-- name    : Disjunctive.LiftProject.mip_cut_lifting_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:14.993254+00:00
-- url     : https://prove2.me/theorems/08382a40-0ed4-4435-aa83-f8bac0b5c542
-- title:
--   Theorem 6.4 — strengthening a lift-and-project cut into a cut valid for the whole mixed 0-1 program
-- statement:
--   This is Theorem 6.4 of Balas's *Disjunctive Programming*. Let $P = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_k \le 1$ ($k \in N'$), and let $\alpha x \ge \beta$ be a lift-and-project cut from $(\mathrm{CGLP})_j$ for a 0-1 variable $j \in N'$: multipliers $u, v \ge 0$, $u_0, v_0 > 0$ with $\beta = u\tilde b = v\tilde b + v_0$ and $\alpha_i = \max\{\alpha^1_i, \alpha^2_i\}$, where $\alpha^1 = u\tilde A - u_0 e_j$, $\alpha^2 = v\tilde A + v_0 e_j$. For $k \in N'$ put $\bar m_k = (\alpha^2_k - \alpha^1_k)/(u_0 + v_0)$ and
--
--   $$\gamma_k = \min\{\alpha^1_k + u_0\lceil \bar m_k\rceil,\ \alpha^2_k - v_0\lfloor \bar m_k\rfloor\}\ (k \in N'), \qquad \gamma_k = \alpha_k\ (k \notin N').$$
--
--   Then $\gamma x \ge \beta$ is valid for the mixed 0-1 feasible set $\{x \in P : x_k \in \{0,1\},\ k \in N'\}$.
--
--   **Formalization Note.** The retired version neither had the bound rows (in particular $x \ge 0$, without which coefficientwise domination proves nothing) nor required $j \in N'$; with $N' = \emptyset$, $P = \mathbb R$ it failed at $x = -1$. Throughout Chapter 6 the LP relaxation is $P = \{x : \tilde A x \ge \tilde b\}$ with the inequalities $x \ge 0$ and $x_j \le 1$ ($j \in N'$) included in $\tilde A x \ge \tilde b$. This is now the explicit hypothesis `HasBoundRows Atil btil N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $P$. The disjunction variable $j$ is a 0-1 variable ($j \in N'$). The clause for $k \notin N'$ is now written $\gamma_k = \alpha_k$ as in the book (equivalent to the former $\max\{\alpha^1_k, \alpha^2_k\}$ through `hAlpha`). $u_0, v_0 > 0$ remains an explicit hypothesis, needed for $\bar m_k$.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §6.5, p. 86, Theorem 6.4

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows

namespace Disjunctive.LiftProject

/-- Theorem 6.4 (Balas, *Disjunctive Programming*, Springer 2018, §6.5, p. 86): let
`P = {x : Ãx ≥ b̃}` be the LP relaxation of a mixed 0-1 program with 0-1 index set `N'`, the bound
rows `x ≥ 0` and `x_k ≤ 1` (`k ∈ N'`) being rows of `Ãx ≥ b̃` (`HasBoundRows`), and let
`αx ≥ β` be a lift-and-project cut from `(CGLP)_j` for a 0-1 variable `j ∈ N'`: `u, v ≥ 0`,
`u₀, v₀ > 0`, `β = u b̃ = v b̃ + v₀`, `α_i = max{α¹_i, α²_i}` with `α¹ = uÃ - u₀e_j`,
`α² = vÃ + v₀e_j`. With `m̄_k := (α²_k - α¹_k)/(u₀ + v₀)`, the strengthened inequality `γx ≥ β`,
`γ_k = min{α¹_k + u₀⌈m̄_k⌉, α²_k - v₀⌊m̄_k⌋}` (`k ∈ N'`), `γ_k = α_k` (`k ∉ N'`), is valid for
the mixed 0-1 feasible set `{x ∈ P : x_k ∈ {0,1}, k ∈ N'}`.
Corrected: the retired version allowed systems without the bound rows (in particular without
`x ≥ 0`) and a disjunction index `j` outside `N'`. -/
theorem mip_cut_lifting_v2 {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Nprime : Finset (Fin n)) (hP : HasBoundRows Atil btil Nprime)
    (j : Fin n) (hj : j ∈ Nprime)
    (u v : Fin m → ℝ) (u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (α : Fin n → ℝ) (β : ℝ)
    (hAlpha : ∀ i, α i = max (Alpha1_64 Atil u u0 j i) (Alpha2_64 Atil v v0 j i))
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbeta1 : β = ∑ ρ, u ρ * btil ρ) (hbeta2 : β = (∑ ρ, v ρ * btil ρ) + v0)
    (γ mbar : Fin n → ℝ)
    (hmbar : ∀ k ∈ Nprime, mbar k = (Alpha2_64 Atil v v0 j k - Alpha1_64 Atil u u0 j k) / (u0 + v0))
    (hgamma1 : ∀ k ∈ Nprime, γ k = min (Alpha1_64 Atil u u0 j k + u0 * (⌈mbar k⌉ : ℝ))
      (Alpha2_64 Atil v v0 j k - v0 * (⌊mbar k⌋ : ℝ)))
    (hgamma2 : ∀ k ∉ Nprime, γ k = α k) :
    ∀ x ∈ MIPDisjunctiveSet Atil btil Nprime, β ≤ dotProduct γ x := by sorry

end Disjunctive.LiftProject
