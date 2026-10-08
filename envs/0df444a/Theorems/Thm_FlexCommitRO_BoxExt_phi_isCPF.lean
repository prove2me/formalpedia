-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_phi_isCPF
-- name    : FlexCommitRO.BoxExt.phi_isCPF
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:38.861476+00:00
-- url     : https://prove2.me/theorems/1ed962a0-0677-42ff-9627-beab3323b858
-- title:
--   Item (a), proof of Lemma 2, p. 270 — φ and f̃_T = f_T + φ are c.p.f.s when D_T is a nonempty polytope
-- statement:
--   In the setting of the worst-case multistage problem of Lemma 2, fix a stage index $T$ and suppose $f_T$ and $f_{T+1}$ are convex polyhedral functions and $D_T = \operatorname{conv} P$ for a finite nonempty set $P \subset \mathbb R^{n_T}$. Let
--   $$
--   \Phi_T(s_T, d_T) = \min\{f_{T+1}(s_{T+1}) : A_{T+1}s_{T+1} \ge B_{T+1}d_T + C_{T+1}s_T + b_{T+1},\ \|s_{T+1}\|_\infty \le R\},\qquad \varphi(s_T) = \max_{d_T \in D_T} \Phi_T(s_T, d_T).
--   $$
--   Then $\varphi$ and $\tilde f_T = f_T + \varphi$ are convex polyhedral functions.
--
--   This is item (a) of the inductive step of Lemma 2: the reduced problem $(P_+)$ again satisfies the lemma's hypotheses.
--
--   **Formalization Note** The page says "$\varphi(\cdot)$ is a cumulative probability function"; this is a slip for "c.p.f." (convex polyhedral function), which is what is stated. Nonemptiness of $P$ is Lemma 2's standing $F_\tau \neq \emptyset$; without it $\varphi \equiv -\infty$, which is not a c.p.f. Lean's `B T`, `C T` are the paper's $B_{T+1}$, $C_{T+1}$; `phi … D T` takes the maximum over `D T`.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 270, Appendix, proof of Lemma 2, item (a)

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
open Matrix

namespace FlexCommitRO.BoxExt

theorem phi_isCPF {n m k : ℕ → ℕ}
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (D : (τ : ℕ) → Set (Fin (n τ) → ℝ)) (T : ℕ)
    (hfT : IsCPF (f T)) (hfT1 : IsCPF (f (T + 1)))
    (P : Finset (Fin (n T) → ℝ)) (hP : P.Nonempty) (hD : D T = convexHull ℝ (P : Set (Fin (n T) → ℝ))) :
    IsCPF (phi A B C b f R D T) ∧ IsCPF (f T + phi A B C b f R D T) := by sorry

end FlexCommitRO.BoxExt
