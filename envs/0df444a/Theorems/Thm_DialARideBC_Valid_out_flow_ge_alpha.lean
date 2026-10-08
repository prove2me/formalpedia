-- Prove2me | Theorems.Thm_DialARideBC_Valid_out_flow_ge_alpha
-- name    : DialARideBC.Valid.out_flow_ge_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:37.087136+00:00
-- url     : https://prove2.me/theorems/dd17fc8e-1422-497f-a614-e4597c891686
-- title:
--   Proof of Proposition 5, p. 578 — x(δ⁺(H)) ≥ α, the number of tight teeth
-- statement:
--   Consider a DARP instance with $n$ users and a feasible solution with total arc flows $x_{ij}$. Let $i_1,\dots,i_m$ be $m$ distinct users and let $H \subseteq P \cup D$ and $T_1,\dots,T_m \subseteq P \cup D$ be node sets such that $\{i_h, n+i_h\} \subseteq T_h$ and $H \cap T_h = \{i_h\}$ for $h = 1,\dots,m$. Let
--   $$\alpha = \bigl|\{h \in \{1,\dots,m\} : x(T_h) = |T_h| - 1\}\bigr|$$
--   be the number of teeth $T_h$ on which the subtour constraint is tight. Then
--   $$x(\delta^+(H)) \ge \alpha,$$
--   where $x(\delta^+(H)) = \sum_{i\in H}\sum_{j \in N\setminus H} x_{ij}$.
--
--   This is the step of the proof of Proposition 5 that converts tightness of the teeth into flow leaving the handle.
--
--   **Formalization Note.** The users are indexed by `Fin m` and required to be distinct (injective), as "$m$ users" means on the page; the complement is taken in $N$, so it contains the depots.
-- source:
--   Cordeau, A Branch-and-Cut Algorithm for the Dial-a-Ride Problem, Oper. Res. 54(3) (2006), p. 578, proof of Proposition 5, fourth and fifth sentences

import Mathlib
import Definitions.Def_DialARideBC_Valid_Model

namespace DialARideBC.Valid

theorem out_flow_ge_alpha {n : ℕ} {K : Type} [Fintype K] (I : Instance n K) (s : Solution I)
    (m : ℕ) (u : Fin m → ℕ) (hu : Function.Injective u) (huP : ∀ h, u h ∈ P n)
    (H : Finset ℕ) (hH : H ⊆ PD n) (T : Fin m → Finset ℕ) (hT : ∀ h, T h ⊆ PD n)
    (hiT : ∀ h, u h ∈ T h ∧ n + u h ∈ T h) (hHT : ∀ h, H ∩ T h = {u h}) :
    ((Finset.univ.filter fun h => xset s.x (T h) = ((T h).card : ℝ) - 1).card : ℝ) ≤ xOut n s.x H := by sorry

end DialARideBC.Valid
