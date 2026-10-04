-- Prove2me | Theorems.Thm_Disjunctive_LiftProject_mip_cut_lifting
-- name    : Disjunctive.LiftProject.mip_cut_lifting
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:36:53.827166+00:00
-- url     : https://prove2.me/theorems/c99fe48d-9a53-440c-ae50-1b6d8dde82c6
-- title:
--   Theorem 6.4 — the general mixed-integer cut-lifting formula
-- statement:
--   This is Theorem 6.4 of Balas's *Disjunctive Programming*, the goal theorem of this mission:
--   strengthening a lift-and-project cut derived from a single 0-1 disjunction into a cut valid for
--   the *entire* mixed 0-1 program, using integrality of every other 0-1 variable.
--
--   Let $\alpha x \ge \beta$ be a lift-and-project cut from `(CGLP)_j` with $\alpha_i =
--   \max\{\alpha^1_i,\alpha^2_i\}$ (eq. (6.4), using the *full*, not row-restricted, multipliers
--   $u,v,u_0,v_0$ with $u_0,v_0 > 0$). For $k \in N'$ (the integer-constrained variables), define
--
--   $$
--   \bar m_k := \frac{\alpha^2_k - \alpha^1_k}{u_0 + v_0}.
--   $$
--
--   Then $\gamma x \ge \beta$ is valid for the *whole* mixed 0-1 program (not merely for the
--   disjunction on $j$), where
--
--   $$
--   \gamma_k = \min\{\alpha^1_k + u_0 \lceil \bar m_k \rceil,\ \alpha^2_k - v_0 \lfloor \bar
--   m_k \rfloor\} \quad (k \in N'), \qquad \gamma_k = \alpha_k \quad (k \notin N').
--   $$
--
--   The idea: since $x_j \le 0 \lor x_j \ge 1$ is valid whenever the original disjunction is, so is
--   $x_j - mx \le 0 \lor x_j - mx \ge 1$ for any integer vector $m$ supported on $N'$; choosing each
--   $m_k$ to make the two candidate coefficients as equal as possible (rounding $\bar m_k$ up or
--   down, whichever is smaller) minimizes the resulting coefficient — turning a cut valid for one
--   disjunction into one valid for the conjunction of all of them, i.e. for the full integer program.
--
--   **Formalization Note.** $u_0, v_0 > 0$ is stated as an explicit hypothesis (needed for
--   $\bar m_k$'s division to be well-posed), matching `BRIEF.md`'s flag that this positivity is
--   implicit in the CGLP feasibility setup rather than a free-standing assumption. The conclusion is
--   stated as genuine validity for `MIPDisjunctiveSet` (imposing $0/1$ on every $k \in N'$
--   simultaneously), not merely as the closed-form formula for $\gamma$, matching the theorem's own
--   "then $\gamma x \ge \beta$ is valid for (MIP)" conclusion.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 86, Theorem 6.4

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic

namespace Disjunctive.LiftProject

/-- Theorem 6.4 (Balas §6.5, p. 86, eq. (6.5)-(6.6)): strengthening a lift-and-project cut
`αx ≥ β` from `(CGLP)_j` (with `α_i = max{α¹_i,α²_i}`) using integrality on the variables `N'`
yields a cut `γx ≥ β` valid for the full mixed 0-1 program, not merely for the single disjunction
on `j`. The premise is that `αx ≥ β` *is* a lift-and-project cut from `(CGLP)_j`: `u, v ≥ 0`,
`β = u b̃ = v b̃ + v₀` and `α_i = max{α¹_i, α²_i}`, the inequality form of (6.3) on p. 85. Bare
validity of `αx ≥ β` with unconstrained multipliers does not give a valid lifted cut: with
`n = 1`, `N' = {j}`, `K = {x_j = 1}`, `u = v = 0`, `u₀ = v₀ = 1`, `β = 1/2` the lifted cut reads
`0 ≥ 1/2` at the feasible point `x_j = 1`. -/
theorem mip_cut_lifting {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (j : Fin n) (Nprime : Finset (Fin n))
    (u v : Fin m → ℝ) (u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (α : Fin n → ℝ) (β : ℝ)
    (hAlpha : ∀ i, α i = max (Alpha1_64 Atil u u0 j i) (Alpha2_64 Atil v v0 j i))
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbeta1 : β = ∑ ρ, u ρ * btil ρ) (hbeta2 : β = (∑ ρ, v ρ * btil ρ) + v0)
    (γ mbar : Fin n → ℝ)
    (hmbar : ∀ k ∈ Nprime, mbar k = (Alpha2_64 Atil v v0 j k - Alpha1_64 Atil u u0 j k) / (u0 + v0))
    (hgamma1 : ∀ k ∈ Nprime, γ k = min (Alpha1_64 Atil u u0 j k + u0 * (⌈mbar k⌉ : ℝ))
      (Alpha2_64 Atil v v0 j k - v0 * (⌊mbar k⌋ : ℝ)))
    (hgamma2 : ∀ k ∉ Nprime, γ k = max (Alpha1_64 Atil u u0 j k) (Alpha2_64 Atil v v0 j k)) :
    ∀ x ∈ MIPDisjunctiveSet Atil btil Nprime, β ≤ dotProduct γ x := by sorry

end Disjunctive.LiftProject
