-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_2
-- name    : BalancedFairAlloc.Existence.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:47.547173+00:00
-- url     : https://prove2.me/theorems/9b16f474-17bd-4dba-9f38-7e4c12efe90d
-- title:
--   Lemma 2 — KKM lemma, closed-set form with the face condition
-- statement:
--   Let $\Delta=\{w\in\mathbb R^n_{\ge0}:\sum_iw_i=1\}$ and let $F_1,\dots,F_n\subseteq\Delta$ be closed sets with $\bigcup_iF_i=\Delta$. If for every nonempty $T\subseteq N$
--
--   $$\Delta(T)=\{w\in\Delta: w_i=0\text{ for }i\notin T\}\subseteq\bigcup_{i\in T}F_i,$$
--
--   then $\bigcap_iF_i\neq\emptyset$.
--
--   This is the topological tool of §3.5: applied to the label sets, it yields one weight vector $w^*$ at which every agent has a witness allocation of minimum label.
--
--   Differences from the source:
--   - encoding: Δ ⊆ ℝ^n, F_i ⊆ Δ closed, T ⊆ N nonempty → `stdSimplex ℝ (Fin n)`, `IsClosed (F i)` in ℝ^n with `F i ⊆ Δ`, T a nonempty `Finset (Fin n)`; reason: same objects on the source domain
--   - generalization: the agent set has n ≥ 1 → n may also be 0; reason: at n = 0 the simplex is empty but the ambient intersection over no sets is all of ℝ⁰, a singleton; the conclusion remains true and every source instance is retained
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 11 (PDF 13), Lemma 2

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

namespace BalancedFairAlloc.Existence

theorem lemma_2 (n : ℕ) (F : Fin n → Set (Fin n → ℝ))
    (hsub : ∀ i, F i ⊆ stdSimplex ℝ (Fin n)) (hclosed : ∀ i, IsClosed (F i))
    (hcover : (⋃ i, F i) = stdSimplex ℝ (Fin n))
    (hface : ∀ T : Finset (Fin n), T.Nonempty → simplexFace T ⊆ ⋃ i ∈ T, F i) :
    (⋂ i, F i).Nonempty := by sorry

end BalancedFairAlloc.Existence
