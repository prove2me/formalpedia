-- Prove2me | Theorems.Thm_Disjunctive_LiftProject_cglp_lifting_from_restricted_v2
-- name    : Disjunctive.LiftProject.cglp_lifting_from_restricted_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:21.771424+00:00
-- url     : https://prove2.me/theorems/ff07960b-7754-463f-85ff-ed881df3db88
-- title:
--   Theorem 6.2 — lifting an optimal solution of the restricted CGLP to an optimal solution of the full CGLP
-- statement:
--   This is Theorem 6.2 of Balas's *Disjunctive Programming* (from Balas, Ceria and Cornuéjols [19]). Let $P = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$, $x_k \le 1$ ($k \in N'$). Let $\bar x$ be the point to be cut off, $R$ the subspace in which the cut is generated (the variables outside $R$ being at their lower bound, $\bar x_i = 0$ for $i \notin R$), and $j \in N' \cap R$ the disjunction variable. The restricted problem $(\mathrm{CGLP})^R_j$ uses the columns in $R$ and the rows $M_R$, obtained by deleting bound rows $x_h \ge 0$, $-x_h \ge -1$ of variables $h \notin R$ (rows that are trivial in the subspace $x_h = 0$). Both CGLPs minimize $\alpha\bar x - \beta$ under the normalization $\beta \in \{1,-1\}$.
--
--   If $w^R = (\alpha^R, \beta, u^R, u^R_0, v^R, v^R_0)$ is optimal for $(\mathrm{CGLP})^R_j$, then $\bar w$ defined by $\bar u = u^R$, $\bar v = v^R$ on $M_R$ and $0$ on the other rows, $\bar u_0 = u^R_0$, $\bar v_0 = v^R_0$, the multipliers of the lower-bound rows $x_i \ge 0$, $i \notin R$,
--
--   $$\bar u_{m+i} = \max\{0, \alpha^2_i - \alpha^1_i\}, \qquad \bar v_{m+i} = \max\{0, \alpha^1_i - \alpha^2_i\} \qquad (\alpha^1_i = u^R\tilde A^R_i,\ \alpha^2_i = v^R \tilde A^R_i),$$
--
--   and $\bar\alpha_i = \alpha^R_i$ ($i \in R$), $\bar\alpha_i = \alpha^1_i + \bar u_{m+i} = \max\{\alpha^1_i, \alpha^2_i\}$ ($i \notin R$), is a feasible and optimal solution of $(\mathrm{CGLP})_j$.
--
--   **Formalization Note.** The retired version (Open) was false: it copied $u^R, v^R$ on every row although the restricted problem leaves their values outside $M_R$ unconstrained, and it put no relation between $\bar x$, $R$, $M_R$ and $j$; it also lacked the bound rows and the normalization, so its optimality clause could only hold with optimal value $0$. The new statement: (i) sets $\bar u = \bar v = 0$ on rows outside $M_R$; (ii) assumes $\bar x_i = 0$ for $i \notin R$ (variables outside the subspace at their lower bound, w.l.o.g. after complementing, as in [19]), $j \in R \cap N'$, and that the rows deleted from $M_R$ are bound rows of variables $h \notin R$; (iii) Throughout Chapter 6 the LP relaxation is $P = \{x : \tilde A x \ge \tilde b\}$ with the inequalities $x \ge 0$ and $x_j \le 1$ ($j \in N'$) included in $\tilde A x \ge \tilde b$. This is now the explicit hypothesis `HasBoundRows Atil btil N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $P$. (iv) uses the normalization $\beta \in \{1,-1\}$ of [19] (normalization (i)), under which Balas states that the lifted cut is exactly the one the full CGLP produces; the CGLP system `IsCGLPFeasible` itself has no normalization. The lower-bound rows carrying $\bar u_{m+i}, \bar v_{m+i}$ are represented, as before, by fresh unit rows (`AtilExt`, `BtilExt`).
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §6.4, p. 84, Theorem 6.2; normalization and subspace conventions as in Balas, Ceria, Cornuéjols, Math. Prog. 58 (1993) 295-324, and Balas, Ann. Oper. Res. 140 (2005), §6 'Cut lifting'

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows

namespace Disjunctive.LiftProject

/-- Theorem 6.2 (Balas, *Disjunctive Programming*, Springer 2018, §6.4, p. 84, from [19]): let
`P = {x : Ãx ≥ b̃}` be the LP relaxation of a mixed 0-1 program with 0-1 index set `N'`, the bound
rows `x ≥ 0`, `x_k ≤ 1` (`k ∈ N'`) being rows of `Ãx ≥ b̃` (`HasBoundRows`), let `x̄` be the
point to be cut off and `R` the subspace of variables in which the cut is generated, the
variables outside `R` being at their lower bound (`x̄_i = 0`, `i ∉ R`) and the disjunction
variable `j ∈ N'` lying in `R`. The reduced problem `(CGLP)^R_j` uses the columns `R` and the rows
`M_R`, obtained by deleting (some of) the bound rows `x_h ≥ 0`, `-x_h ≥ -1` of the variables
`h ∉ R` (which are trivial in the subspace `x_h = 0`).
`(CGLP)` is normalized by `β ∈ {1,-1}` (normalization (i) of [19]) and minimizes `αx̄ − β`.
If `w^R = (α^R, β, u^R, u^R_0, v^R, v^R_0)` is optimal for `(CGLP)^R_j`, then `w̄` with
`ū = u^R` on `M_R`, `ū = 0` on the other rows, `ū₀ = u^R_0`, `v̄₀ = v^R_0`, new multipliers
`ū_{m+i} = max{0, α²_i − α¹_i}`, `v̄_{m+i} = max{0, α¹_i − α²_i}` on the lower-bound rows `x_i ≥ 0`
of the variables `i ∉ R` (`α¹_i = u^R Ã^R_i`, `α²_i = v^R Ã^R_i`), `ᾱ_i = α^R_i` (`i ∈ R`) and
`ᾱ_i = α¹_i + ū_{m+i}` (`i ∉ R`) is feasible and optimal for `(CGLP)_j`. The lower-bound rows
used by `w̄` are represented as fresh unit rows (`AtilExt`, `BtilExt`).
Corrected: the retired version let `u^R, v^R` keep arbitrary values on rows outside `M_R`, let
`M_R`, `R` and `x̄` be unrelated to each other and `j ∉ R`, had no bound rows and no
normalization, which made it false (and its optimality clause degenerate). -/
theorem cglp_lifting_from_restricted_v2 {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hP : HasBoundRows Atil btil Nprime) (MR : Finset M) (R : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ Nprime) (hjR : j ∈ R)
    (hMR : ∀ ρ ∉ MR, ∃ h ∉ R, (Atil ρ = Pi.single h 1 ∧ btil ρ = 0) ∨
      (Atil ρ = -Pi.single h 1 ∧ btil ρ = -1))
    (xbar : Fin n → ℝ) (hxbar : ∀ i ∉ R, xbar i = 0)
    (αR : Fin n → ℝ) (uR vR : M → ℝ) (u0R v0R βR : ℝ)
    (hfeas : IsCGLPRFeasible Atil btil MR R j αR uR u0R vR v0R βR) (hnorm : βR = 1 ∨ βR = -1)
    (hopt : ∀ (α' : Fin n → ℝ) (u' v' : M → ℝ) (u0' v0' β' : ℝ),
      IsCGLPRFeasible Atil btil MR R j α' u' u0' v' v0' β' → (β' = 1 ∨ β' = -1) →
        dotProduct αR xbar - βR ≤ dotProduct α' xbar - β') :
    ∃ (α : Fin n → ℝ) (u v : M ⊕ Fin n → ℝ),
      (∀ ρ : M, u (Sum.inl ρ) = (if ρ ∈ MR then uR ρ else 0) ∧
        v (Sum.inl ρ) = (if ρ ∈ MR then vR ρ else 0)) ∧
      (∀ i ∉ R, u (Sum.inr i) =
          (if Alpha1 Atil uR MR i < Alpha2 Atil vR MR i
            then Alpha2 Atil vR MR i - Alpha1 Atil uR MR i else 0) ∧
        v (Sum.inr i) =
          (if Alpha2 Atil vR MR i < Alpha1 Atil uR MR i
            then Alpha1 Atil uR MR i - Alpha2 Atil vR MR i else 0)) ∧
      (∀ i ∈ R, u (Sum.inr i) = 0 ∧ v (Sum.inr i) = 0) ∧
      (∀ i ∈ R, α i = αR i) ∧
      (∀ i ∉ R, α i = Alpha1 Atil uR MR i + u (Sum.inr i)) ∧
      IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α u u0R v v0R βR ∧
      ∀ (α' : Fin n → ℝ) (u' v' : M ⊕ Fin n → ℝ) (u0' v0' β' : ℝ),
        IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α' u' u0' v' v0' β' →
          (β' = 1 ∨ β' = -1) →
          dotProduct α xbar - βR ≤ dotProduct α' xbar - β' := by sorry

end Disjunctive.LiftProject
