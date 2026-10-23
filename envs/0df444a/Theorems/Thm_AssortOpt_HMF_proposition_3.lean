-- Prove2me | Theorems.Thm_AssortOpt_HMF_proposition_3
-- name    : AssortOpt.HMF.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:14.594552+00:00
-- url     : https://prove2.me/theorems/e57755c0-5e21-46bf-abf8-1a6fe477bc4b
-- title:
--   Proposition 3, p. 14 (corrected: f(∅) = 0 in the "Moreover" clause) — OPT^f has a boolean optimum, and φ_j(H) = f(H ∪ {j}) has REV[φ] = REV[f]
-- statement:
--   Let $\mathcal L, p$ be a list distribution with prices $r_j \ge 0$.
--
--   1. The problem $\mathsf{OPT}^f$ (maximize $\mathsf{REV}[f]$ over increasing $f : 2^N \to [0,1]$) has an optimal solution that is an increasing **boolean** set function, $f : 2^N \to \{0,1\}$.
--   2. For every increasing boolean $f : 2^N \to \{0,1\}$ with $f(\emptyset) = 0$, setting
--   $$\phi_j(H) = f(H \cup \{j\}), \qquad j \in N,\ H \subseteq N \setminus \{j\} \qquad (11)$$
--   defines a monotone stopping policy $\phi$ with $\mathsf{REV}[\phi] = \mathsf{REV}[f]$.
--   3. Therefore $\mathsf{OPT}^f \le \mathsf{OPT}^\phi$: for every increasing $g : 2^N \to [0,1]$ there is a monotone stopping policy $\phi$ with $\mathsf{REV}[g] \le \mathsf{REV}[\phi]$.
--
--   This is the last step of the relaxation chain $\mathsf{OPT}^S \le \mathsf{OPT}^x \le \mathsf{OPT}^f \le \mathsf{OPT}^\phi$: it turns the linear relaxation into an optimal stopping problem on the tree of prefixes.
--
--   **Formalization Note** The policy (11) is the boolean `decide (f (insert j H) = 1)`.
--
--   Differences from the source:
--   - correction: "for any increasing boolean $f$, (11) gives $\mathsf{REV}[\phi] = \mathsf{REV}[f]$" → clause 2 also assumes $f(\emptyset) = 0$; reason: false for $f \equiv 1$: with $n = 1$, $\mathcal L = \{(1)\}$, $p = 1$, $r_1 = 1$, $\mathsf{REV}[f] = r_1(f(\{1\}) - f(\emptyset)) = 0$ but $\phi_1(\emptyset) = f(\{1\}) = 1$ gives $\mathsf{REV}[\phi] = 1$. Clauses 1 and 3 are stated as printed (if a boolean optimum has $f(\emptyset) = 1$ it is $f \equiv 1$ with revenue $0$, matched by $\phi \equiv 0$), and the $f$ of Proposition 2 has $f(\emptyset) = 0$.
--   - encoding: items $\{1,\dots,n\}$, lists, support $\mathcal L$ with weights $p$ → `Fin n` (0-based), `ListDist` (finite support of `Nodup` lists, $p > 0$ on $\mathcal L$, $\sum p = 1$); reason: same instances.
--   - encoding: "an optimal solution of $\mathsf{OPT}^f$" → an increasing $f$ with $\mathsf{REV}[g] \le \mathsf{REV}[f]$ for every increasing $g$; reason: $\mathsf{OPT}^f$ is a supremum, and this states that it is attained by $f$.
--   - encoding: $\mathsf{OPT}^f \le \mathsf{OPT}^\phi$ → $\forall g$ increasing $\exists \phi$ monotone with $\mathsf{REV}[g] \le \mathsf{REV}[\phi]$; reason: the optimal values are not named; same inequality.
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 14, Proposition 3 (11)

import Mathlib
import Definitions.Def_AssortOpt_HMF_Setting

namespace AssortOpt.HMF

theorem proposition_3 {n : ℕ} (D : ListDist n) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) :
    (∃ f : Finset (Fin n) → ℝ, IsIncreasingSetFn f ∧ (∀ S, f S = 0 ∨ f S = 1) ∧
      ∀ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g → revSetFn D r g ≤ revSetFn D r f) ∧
    (∀ f : Finset (Fin n) → ℝ, IsIncreasingSetFn f → (∀ S, f S = 0 ∨ f S = 1) → f ∅ = 0 →
      IsMonotonePolicy (fun j H => decide (f (insert j H) = 1)) ∧
      revPolicy D r (fun j H => decide (f (insert j H) = 1)) = revSetFn D r f) ∧
    (∀ g : Finset (Fin n) → ℝ, IsIncreasingSetFn g →
      ∃ φ : Policy n, IsMonotonePolicy φ ∧ revSetFn D r g ≤ revPolicy D r φ) := by sorry

end AssortOpt.HMF
