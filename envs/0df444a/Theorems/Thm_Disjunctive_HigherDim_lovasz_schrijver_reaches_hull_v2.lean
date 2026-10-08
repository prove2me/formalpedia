-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_lovasz_schrijver_reaches_hull_v2
-- name    : Disjunctive.HigherDim.lovasz_schrijver_reaches_hull_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:46.601317+00:00
-- url     : https://prove2.me/theorems/a8847557-8fa1-499d-bc36-27b36e3aa2f5
-- title:
--   Theorem 7.5 — iterating the Lovász–Schrijver operator $p$ times reaches the integer hull, $N^p(K) = \mathrm{conv}(K_0)$
-- statement:
--   This is Theorem 7.5 of Balas's *Disjunctive Programming* (cited to Lovász and Schrijver [99]). Let $K = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with $p = |N'|$ 0-1 variables, $K_0 = K \cap \{x_j \in \{0,1\},\ j \in N'\}$, and $N^1(K) = N(K)$, $N^t(K) = N(N^{t-1}(K))$. Then
--
--   $$N^p(K) = \mathrm{conv}(K_0).$$
--
--   The iterates are given by linear systems $(A_t, b_t)$, $t = 0,\dots,p$, with $\{x : A_0 x \ge b_0\} = K$ and $\{x : A_{t+1}x \ge b_{t+1}\} = N(\{x : A_t x \ge b_t\})$, every system containing the bound rows $x \ge 0$, $x_j \le 1$ ($j \in N'$).
--
--   **Formalization Note.** The retired version (Open) allowed systems without the bound rows, the gap that falsified Theorems 7.1, 7.4, 7.6 and 7.7 of the same chapter; with no rows, $N(K) = \mathbb R^n$ and the claim fails already for $p = 1$. Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows. Each $N^t(K) \subseteq K$ lies in the box, so a system for it containing the bound rows always exists (append them as redundant rows); with them the linearized system defining $N$ coincides with Lovász and Schrijver's representation-free cone definition.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.2, p. 93, Theorem 7.5

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Theorem 7.5 (Balas, *Disjunctive Programming*, Springer 2018, §7.2, p. 93, [99]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with `p = |N'|` 0-1 variables,
`N^p(K) = conv(K₀)`, where `N¹(K) := N(K)` and `N^t(K) := N(N^{t-1}(K))`. The iterates are given
by systems `(A t, b t)`, `t = 0,…,p`, with `Poly (A 0) (b 0) = K` and
`Poly (A (t+1)) (b (t+1)) = N(Poly (A t) (b t))`. Every system contains the bound rows `x ≥ 0`,
`x_j ≤ 1` (`j ∈ N'`) (`HasBoundRows`), as `Ãx ≥ b̃` does in the book; each `N^t(K) ⊆ K` lies in
the box, so such a representation always exists (append the redundant bound rows), and it makes
the linearized system of `N` equal to Lovász and Schrijver's representation-free cone
formulation.
Corrected: the retired version allowed systems without the bound rows. -/
theorem lovasz_schrijver_reaches_hull_v2 {n p : ℕ} {mA : Fin (p + 1) → ℕ}
    (A : (t : Fin (p + 1)) → Matrix (Fin (mA t)) (Fin n) ℝ)
    (b : (t : Fin (p + 1)) → Fin (mA t) → ℝ) (Nprime : Finset (Fin n)) (hp : Nprime.card = p)
    (hK : ∀ t, HasBoundRows (A t) (b t) Nprime)
    (hStep : ∀ t : Fin p, Poly (A t.succ) (b t.succ) = NOp (A t.castSucc) (b t.castSucc) Nprime) :
    Poly (A (Fin.last p)) (b (Fin.last p)) = convexHull ℝ (K0Set (A 0) (b 0) Nprime) := by sorry

end Disjunctive.HigherDim
