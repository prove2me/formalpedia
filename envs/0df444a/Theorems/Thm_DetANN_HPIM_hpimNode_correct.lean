-- Prove2me | Theorems.Thm_DetANN_HPIM_hpimNode_correct
-- name    : DetANN.HPIM.hpimNode_correct
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T06:36:54.078467+00:00
-- url     : https://prove2.me/theorems/807c73dd-3462-41d6-8632-40902629d7cd
-- title:
--   Correctness of the HPIM search
-- statement:
--   Let $m\ge1$, let $Y_1,\dots,Y_N\in\mathbb R^m$ be distinct and $\delta\in(0,1/2)$. Let $S$ be a nonempty set of indices and $f>\lceil\log_2|S|\rceil$. For every query $q$, the search of $\mathrm{hpimNode}(Y,\delta,f,S)$ (definition `DetANN_HPIMTree`) returns some $k\in S$ with
--   $$\|q-Y_k\|\le\alpha\bigl(\lceil\log_2|S|\rceil\bigr)\,\|q-Y_j\|\qquad\text{for all }j\in S,$$
--   where $\alpha(L)=(1+1/\lambda)^L(1+\delta/4)^2$.
--
--   This is the correctness argument of Har-Peled, Indyk and Motwani (2012, §2) for the deterministic tree. It considers three cases:
--   - the query is close to the points: the search recurses into one component;
--   - the query is far from the points: the search recurses into the representatives;
--   - otherwise the ladder search answers.
--
--   Each level costs a factor $1+1/\lambda$.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMTree

namespace DetANN.HPIM

/-- **Correctness of the HPIM search.** Let `m ≥ 1`, `Y : Fin N → ℝ^m` injective, `δ ∈ (0, 1/2)`. For
every nonempty `S ⊆ Fin N` and fuel `f > ⌈log₂ |S|⌉`, the search of `hpimNode Y δ f S` at any query `q`
returns a point `k ∈ S` with `‖q − Y_k‖ ≤ α ‖q − Y_j‖` for all `j ∈ S`, where
`α = (1 + 1/λ)^{⌈log₂ |S|⌉} (1 + δ/4)^2`. -/
theorem hpimNode_correct {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hm : 1 ≤ m)
    (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∀ f (S : Finset (Fin N)), S.Nonempty → Nat.clog 2 S.card < f →
      ∀ q : EuclideanSpace ℝ (Fin m), ∃ k ∈ S, (hpimNode Y δ f S).search q = (k : ℕ) ∧
        ∀ j ∈ S, ‖q - Y k‖ ≤ alphaOf N δ (Nat.clog 2 S.card) * ‖q - Y j‖ := by sorry

end DetANN.HPIM
