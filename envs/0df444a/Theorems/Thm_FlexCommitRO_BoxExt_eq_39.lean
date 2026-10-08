-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_eq_39
-- name    : FlexCommitRO.BoxExt.eq_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:43.235827+00:00
-- url     : https://prove2.me/theorems/71bd9155-6496-48b6-bcb3-eaa055609bae
-- title:
--   (39), p. 270 — opt(P[F_0, …, F_{T−1}, D_T]) = opt(P+[F_0, …, F_{T−1}]) = opt(P[F_0, …, F_{T−1}, ext(D_T)])
-- statement:
--   In the worst-case multistage problem of Lemma 2 with horizon $T+1$, suppose $f_1,\dots,f_{T+2}$ are convex polyhedral functions, $F_0,\dots,F_T$ are nonempty, and the last set $D_{T+1} = \operatorname{conv} P$ is the convex hull of a finite nonempty set $P$. Then
--   $$
--   \operatorname{opt}(P[F_0,\dots,F_T, D_{T+1}]) = \operatorname{opt}(P_+[F_0,\dots,F_T]) = \operatorname{opt}(P[F_0,\dots,F_T, \operatorname{ext}(D_{T+1})]),
--   $$
--   where $(P_+[F_0,\dots,F_T])$ is the horizon-$T$ problem in which $f_{T+1}$ is replaced by $f_{T+1} + \varphi$ and $\varphi(s) = \sup_{d \in D_{T+1}} \Phi_{T+1}(s, d)$.
--
--   This is display (39) of the proof of Lemma 2: replacing the last demand set by its extreme points does not change the optimal value.
--
--   **Formalization Note** Stated for horizon $T+1$ (the paper's (39) is at horizon $T$, with $D_T$). The families are $\mathbb N$-indexed with the paper's indices; Lean's `Function.update F (T+1) D` is the family $F_0,\dots,F_T, D_{T+1}$.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 270, Appendix, proof of Lemma 2, item (b), (39)

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem eq_39 {n m k : ℕ → ℕ}
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (F : (τ : ℕ) → Set (Fin (n τ) → ℝ)) (T : ℕ)
    (hf : ∀ t, 1 ≤ t → t ≤ T + 2 → IsCPF (f t))
    (hF : ∀ τ, τ ≤ T → (F τ).Nonempty)
    (DT : Set (Fin (n (T + 1)) → ℝ)) (P : Finset (Fin (n (T + 1)) → ℝ)) (hP : P.Nonempty)
    (hDT : DT = convexHull ℝ (P : Set (Fin (n (T + 1)) → ℝ))) :
    opt (T + 1) A B C b f R (Function.update F (T + 1) DT) =
        opt T A B C b
          (Function.update f (T + 1)
            (f (T + 1) + phi A B C b f R (Function.update F (T + 1) DT) (T + 1))) R F ∧
      opt T A B C b
          (Function.update f (T + 1)
            (f (T + 1) + phi A B C b f R (Function.update F (T + 1) DT) (T + 1))) R F =
        opt (T + 1) A B C b f R (Function.update F (T + 1) (DT.extremePoints ℝ)) := by sorry

end FlexCommitRO.BoxExt
