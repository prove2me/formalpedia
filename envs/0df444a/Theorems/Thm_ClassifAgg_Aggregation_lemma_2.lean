-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_2
-- name    : ClassifAgg.Aggregation.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:17:47.872648+00:00
-- url     : https://prove2.me/theorems/89630320-8d61-4e4b-a80f-1c203c91a3cd
-- title:
--   Lemma 2, p. 153 — if j is admissible then 0 ≤ R_n(G_nkj) − R_n(G_nj) ≤ T_nk(G_nkj, G_nk) and |R_n(G_nkj) − R_n(G_nk)| ≤ T_nk(G_nkj, G_nk)
-- statement:
--   Fix a sample size $n$, a sample, an integer $N$, nested approximating sets $\mathcal N_1\subseteq\dots\subseteq\mathcal N_N$, complexities $\rho_1,\dots,\rho_N$, empirical risk minimizers $G_{nk}\in\mathcal N_k$ ($k=1,\dots,N$) and pseudoclassifiers $G_{nkj}$ as in the procedure of Section 3. If the index $j\in\{1,\dots,N\}$ is admissible, then for all $k$ with $j\le k\le N$,
--   $$0\le R_n(G_{nkj})-R_n(G_{nj})\le T_{nk}(G_{nkj},G_{nk}),\tag{27}$$
--   $$|R_n(G_{nkj})-R_n(G_{nk})|\le T_{nk}(G_{nkj},G_{nk}).\tag{28}$$
--
--   This deterministic observation is what lets the proof of Theorem 3 compare the adaptive classifier with the oracle classifier $G_{nj^*}$.
--
--   **Formalization Note** The statement is deterministic: it holds for one fixed sample, and the empirical risk minimization is assumed at that sample only.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Lemma 2, p. 153; proof p. 158

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Setup

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_2 {d n : ℕ} (N : ℕ) (net : ℕ → Set (Set (E d))) (ρ : ℕ → ℝ)
    (Ghat : ℕ → (Fin n → E d × Bool) → Set (E d))
    (Gtil : ℕ → ℕ → (Fin n → E d × Bool) → Set (E d))
    (s : Fin n → E d × Bool)
    (hnest : ∀ j k, 1 ≤ j → j ≤ k → k ≤ N → net j ⊆ net k)
    (hERM : ∀ k, 1 ≤ k → k ≤ N →
      Ghat k s ∈ net k ∧ ∀ G ∈ net k, empRisk s (Ghat k s) ≤ empRisk s G)
    (hsel : IsPseudoSel n net ρ Ghat Gtil)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (hadm : Admissible n N net ρ Ghat j s) :
    ∀ k, j ≤ k → k ≤ N →
      (0 ≤ empRisk s (Gtil k j s) - empRisk s (Ghat j s) ∧
        empRisk s (Gtil k j s) - empRisk s (Ghat j s)
          ≤ threshold n (ρ k) (Gtil k j s) (Ghat k s) s) ∧
      |empRisk s (Gtil k j s) - empRisk s (Ghat k s)|
        ≤ threshold n (ρ k) (Gtil k j s) (Ghat k s) s := by sorry

end ClassifAgg.Aggregation
