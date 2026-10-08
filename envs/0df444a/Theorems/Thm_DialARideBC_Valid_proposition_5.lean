-- Prove2me | Theorems.Thm_DialARideBC_Valid_proposition_5
-- name    : DialARideBC.Valid.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:52.184221+00:00
-- url     : https://prove2.me/theorems/49b05a02-3f4f-4a60-9658-02f8ba69e8df
-- title:
--   Proposition 5, p. 578 — the generalized order-matching inequality (39) is valid for the DARP
-- statement:
--   Consider a DARP instance with $n$ users and vehicle set $K$, and any feasible solution with total arc flows $x_{ij} = \sum_{k\in K} x^k_{ij}$. Let $i_1,\dots,i_m$ be $m$ distinct users and let $H \subseteq P\cup D$ and $T_h \subseteq P \cup D$, $h = 1,\dots,m$, be node sets such that
--   $$\{i_h, n+i_h\} \subseteq T_h \qquad\text{and}\qquad H \cap T_h = \{i_h\}\qquad (h = 1,\dots,m).$$
--   Then the **generalized order-matching inequality** holds:
--   $$x(H) + \sum_{h=1}^m x(T_h) \le |H| + \sum_{h=1}^m |T_h| - 2m. \tag{39}$$
--
--   It generalizes the order-matching constraints of Ruland and Rodin by replacing the arcs $(i_h, n+i_h)$ with node sets, and by Remark 2 it is stronger than the corresponding TSP comb inequality. The paper's proof closes with: "Finally, because $x(T_h) \le |T_h| - 2$ for the remaining $m-\alpha$ sets, one may conclude that $x(H) + \sum_{h=1}^m x(T_h) \le |H| - \alpha + \sum_{h=1}^m (|T_h| - 1) - (m-\alpha)$, which simplifies to expression (39)."
--
--   **Formalization Note.** The printed display (39) has a stray "+" before "$\le$"; the Lean has no extra term. The page's "$\subset$" is non-strict inclusion. Users are indexed by `Fin m` and required to be distinct: with a repeated user the inequality fails (e.g. $H = \{i\}$, $T_1 = T_2 = \{i, n+i\}$ and a route $i \to n+i$ give $2 \not\le 1$). The right-hand side is computed in $\mathbb R$.
-- source:
--   Cordeau, A Branch-and-Cut Algorithm for the Dial-a-Ride Problem, Oper. Res. 54(3) (2006), p. 578, §4.6, Proposition 5 and (39)

import Mathlib
import Definitions.Def_DialARideBC_Valid_Model

namespace DialARideBC.Valid

theorem proposition_5 {n : ℕ} {K : Type} [Fintype K] (I : Instance n K) (s : Solution I)
    (m : ℕ) (u : Fin m → ℕ) (hu : Function.Injective u) (huP : ∀ h, u h ∈ P n)
    (H : Finset ℕ) (hH : H ⊆ PD n) (T : Fin m → Finset ℕ) (hT : ∀ h, T h ⊆ PD n)
    (hiT : ∀ h, u h ∈ T h ∧ n + u h ∈ T h) (hHT : ∀ h, H ∩ T h = {u h}) :
    xset s.x H + ∑ h, xset s.x (T h) ≤ (H.card : ℝ) + ∑ h, ((T h).card : ℝ) - 2 * m := by sorry

end DialARideBC.Valid
