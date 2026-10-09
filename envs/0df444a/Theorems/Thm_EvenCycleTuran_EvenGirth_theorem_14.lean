-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_theorem_14
-- name    : EvenCycleTuran.EvenGirth.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:08.603856+00:00
-- url     : https://prove2.me/theorems/b996cab0-17ef-4e73-99e5-47916039fe63
-- title:
--   Theorem 14, p. 6 — for k > l ≥ 2, m ≥ 2, 2k ≠ ml: ex(n, C_{ml}, 𝒞_{2l−1} ∪ {C₂ₖ}) = Θ(n^m)
-- statement:
--   Let $k$, $l$, $m$ be integers with $k>l\ge2$, $m\ge2$ and $2k\ne ml$. Write $\mathcal C_{2l-1}=\{C_3,C_4,\dots,C_{2l-1}\}$. Then, as $n\to\infty$,
--
--   $$\mathrm{ex}\big(n,C_{ml},\mathcal C_{2l-1}\cup\{C_{2k}\}\big)=\Theta(n^m),$$
--
--   that is, the maximum number of cycles of length $ml$ in an $n$-vertex graph with no cycle of length $3,4,\dots,2l-1$ and no cycle of length $2k$ is bounded above and below by positive constant multiples of $n^m$, the constants depending on $k$, $l$, $m$.
--
--   For $m=2$ this determines the order of magnitude of the number of $C_{2l}$'s in a $C_{2k}$-free graph of girth $2l$. The lower bound comes from theta graphs, which contain only cycles of lengths $2l$ and $ml$.
--
--   **Formalization Note.** $\Theta$ is Mathlib's `IsTheta` along `atTop` for $n\mapsto \mathrm{ex}(\dots)$ cast to $\mathbb R$ and $n\mapsto n^m$; it is two-sided. The forbidden family is `Set.Icc 3 (2 * l - 1) ∪ {2 * k}`, every length $3,\dots,2l-1$ and $2k$. The hypothesis $l\ge2$ is implicit on the page (which states $k>l$): $\mathcal C_{2l-1}$ is a family of cycles only for $2l-1\ge3$, the theorem concerns graphs of girth $2l$, and at $l=1$ the statement fails (for $m=3$ a $C_{2k}$-free graph has $o(n^3)$ triangles).
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 6, Theorem 14 (restated p. 20; proof §5, pp. 18–24)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem theorem_14 (k l m : ℕ) (hl : 2 ≤ l) (hkl : l < k) (hm : 2 ≤ m) (hne : 2 * k ≠ m * l) :
    (fun n : ℕ => (EvenCycleTuran.C4Count.exCyc n (cycleGraph (m * l)) (Set.Icc 3 (2 * l - 1) ∪ {2 * k}) : ℝ))
      =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ m) := by sorry

end EvenCycleTuran.EvenGirth
