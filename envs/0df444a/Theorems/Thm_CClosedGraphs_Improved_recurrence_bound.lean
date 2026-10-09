-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_recurrence_bound
-- name    : CClosedGraphs.Improved.recurrence_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:36.02123+00:00
-- url     : https://prove2.me/theorems/2a280a95-ed0c-4d67-b456-846180e7128e
-- title:
--   pp. 10–11 — the recurrence's two cases are bounded by F₀(n, c)
-- statement:
--   Let $c\ge2$ be an integer and let $n,\Delta$ be real numbers with $n\ge1$ and $0<\Delta\le n$. With $F_0(m,c)=4^{(c+4)(c-1)/2}m^{2-2^{1-c}}$:
--
--   1. if $\Delta\le\sqrt n$, then $n\,F_0(\Delta,c-1)\le F_0(n,c)$;
--   2. if $\Delta>\sqrt n$, then
--   $$F_0(\Delta,c-1)\,\frac{n}{\Delta}\,2^{c}+F_0(n-\Delta,c)\;\le\;F_0(n,c).$$
--
--   These are the two inequalities "we need to show" in the inductive step of Theorem 3.1: the right-hand sides of the recurrence for $F(n,c)$, with $F$ at the smaller parameters replaced by $F_0$, do not exceed $F_0(n,c)$.
--
--   **Formalization Note** The paper prints this display with base $2$ in place of the base $4$ of $F_0$; the statement here uses $F_0$ as the paper defines it on p. 10. The second case keeps the paper's $n-\Delta$ (the vertex $v$ itself is also deleted, so $n-\Delta-1$ would suffice); $F_0(0,c)=0$.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, pp. 10–11, proof of Theorem 3.1, recurrence and inductive-case display

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
theorem recurrence_bound {c : ℕ} (hc : 2 ≤ c) {n Δ : ℝ} (hn : 1 ≤ n) (hΔ0 : 0 < Δ)
    (hΔn : Δ ≤ n) :
    (Δ ≤ Real.sqrt n → n * F0 Δ (c - 1) ≤ F0 n c) ∧
      (Real.sqrt n < Δ → F0 Δ (c - 1) * (n / Δ) * 2 ^ c + F0 (n - Δ) c ≤ F0 n c) := by sorry
end CClosedGraphs.Improved
