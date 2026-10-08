-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_lemma_2
-- name    : FlexCommitRO.BoxExt.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:42.245803+00:00
-- url     : https://prove2.me/theorems/c8044899-b320-43d2-993f-2e677a0313d2
-- title:
--   Lemma 2, p. 269 — a worst-case multistage problem over convex polytopes has the same optimal value over their extreme points
-- statement:
--   Let $D_\tau \subset \mathbb R^{n_\tau}$, $\tau = 0, 1, \dots, T$, be convex polytopes (convex hulls of finite sets), with $D_0$ a singleton. Consider the worst-case multistage problem $(P[F_0,\dots,F_T])$: minimize over nonanticipative decision rules $S_1(d^0), \dots, S_{T+1}(d^T)$ the worst case over $d \in F_0 \times \dots \times F_T$ of
--   $$
--   f_1(S_1(d^0)) + f_2(S_2(d^1)) + \dots + f_{T+1}(S_{T+1}(d^T))
--   $$
--   subject to $A_1S_1(d^0) \ge b_1$, $A_{t+1}S_{t+1}(d^t) \ge B_{t+1}d_t + C_{t+1}S_t(d^{t-1}) + b_{t+1}$ for $t = 1,\dots,T$, and $\|S_t(d^{t-1})\|_\infty \le R$ for $t = 1,\dots,T+1$. Assume that every $f_t$, $t = 1,\dots,T+1$, is a convex polyhedral function. Then
--   $$
--   \operatorname{opt}(P[D_0,\dots,D_T]) = \operatorname{opt}(P[\operatorname{ext}(D_0),\dots,\operatorname{ext}(D_T)]).
--   $$
--
--   This is the general principle behind Proposition 1: in a multistage worst-case problem with convex polyhedral costs and polyhedral dynamics, nature may be restricted to the vertices of each period's uncertainty polytope.
--
--   **Formalization Note** Families are $\mathbb N$-indexed with the paper's indices; Lean's `B t`, `C t` are the paper's $B_{t+1}$, $C_{t+1}$. Decision rules are functions of the whole trajectory, constrained to agree on trajectories of the uncertainty set that share $d_0,\dots,d_{t-1}$. Optimal values are extended reals. No nonemptiness is assumed beyond $D_0$ being a singleton (an empty polytope makes both sides $-\infty$), and no sign is assumed on $R$ (for $R < 0$ both sides are $+\infty$).
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 269, Appendix, Lemma 2

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem lemma_2 {n m k : ℕ → ℕ}
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (T : ℕ) (D : (τ : ℕ) → Set (Fin (n τ) → ℝ))
    (hD : ∀ τ, τ ≤ T → ∃ P : Finset (Fin (n τ) → ℝ), D τ = convexHull ℝ (P : Set (Fin (n τ) → ℝ)))
    (hD0 : ∃ a, D 0 = {a})
    (hf : ∀ t, 1 ≤ t → t ≤ T + 1 → IsCPF (f t)) :
    opt T A B C b f R D = opt T A B C b f R (fun τ => (D τ).extremePoints ℝ) := by sorry

end FlexCommitRO.BoxExt
