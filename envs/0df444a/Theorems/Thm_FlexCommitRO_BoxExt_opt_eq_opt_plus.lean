-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_opt_eq_opt_plus
-- name    : FlexCommitRO.BoxExt.opt_eq_opt_plus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:30.989855+00:00
-- url     : https://prove2.me/theorems/05a512f6-7202-4ef5-b850-f8462bbf55e6
-- title:
--   Proof of Lemma 2, p. 270 — Bellman reduction: opt(P[F_0, …, F_T]) = opt(P+[F_0, …, F_{T−1}]) with f̃_T = f_T + φ
-- statement:
--   Consider the worst-case multistage problem of Lemma 2 with horizon $T+1$ (stages $S_1,\dots,S_{T+2}$, trajectories in $F_0 \times \dots \times F_{T+1}$). Suppose $f_1,\dots,f_{T+2}$ are convex polyhedral functions and $F_0,\dots,F_{T+1}$ are nonempty. Let $\Phi_{T+1}$ and $\varphi(s_{T+1}) = \sup_{d_{T+1} \in F_{T+1}} \Phi_{T+1}(s_{T+1}, d_{T+1})$ be the last-stage value and its worst case. Then
--   $$
--   \operatorname{opt}(P[F_0,\dots,F_{T+1}]) = \operatorname{opt}(P_+[F_0,\dots,F_T]),
--   $$
--   where $(P_+[F_0,\dots,F_T])$ is the problem with horizon $T$ (stages $S_1,\dots,S_{T+1}$) in which $f_{T+1}$ is replaced by $\tilde f_{T+1} = f_{T+1} + \varphi$.
--
--   This is the Bellman equation the induction of Lemma 2 runs on: the last stage is optimized out, and its worst case is charged to the previous stage.
--
--   **Formalization Note** The statement is written for the step from horizon $T+1$ to $T$ to avoid natural-number subtraction; the paper's version is the step from $T$ to $T-1$. The page writes $(P_+)$ as a minimum over $S_1,\dots,S_{T-1}$ while its constraints and objective use $S_T$, and writes $\tilde f_T(S_T(d^{t-1}))$ for $\tilde f_T(S_T(d^{T-1}))$; the statement uses the intended reading ($(P_+)$ is $(P)$ with one fewer stage). Nonemptiness is required only of $F_0,\dots,F_{T+1}$ and the c.p.f. property only of $f_1,\dots,f_{T+2}$.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 270, Appendix, proof of Lemma 2 (Φ_T, φ, problem (P+[F_0, …, F_{T−1}]))

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem opt_eq_opt_plus {n m k : ℕ → ℕ}
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (F : (τ : ℕ) → Set (Fin (n τ) → ℝ)) (T : ℕ)
    (hf : ∀ t, 1 ≤ t → t ≤ T + 2 → IsCPF (f t))
    (hF : ∀ τ, τ ≤ T + 1 → (F τ).Nonempty) :
    opt (T + 1) A B C b f R F =
      opt T A B C b (Function.update f (T + 1) (f (T + 1) + phi A B C b f R F (T + 1))) R F := by sorry

end FlexCommitRO.BoxExt
