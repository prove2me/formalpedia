-- Prove2me | Theorems.Thm_FeedbackSwitching_lemma_5
-- name    : FeedbackSwitching.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:00.615515+00:00
-- url     : https://prove2.me/theorems/dfa217b9-1508-4be8-94d4-7d7c27341609
-- title:
--   Lemma 5 — the one-sided tournament scores (21) form a score rule
-- statement:
--   Fix a tournament orientation. Let $P$ be a transition matrix reversible with respect to a positive probability vector $p$, with $P(s\mid s)\ge\tfrac12$ for every $s$. Then the scores of Eq. (21),
--   $$
--   d_t(s,j)=\Delta_t(s,j)\ (s\to j),\qquad d_t(s,j)=0\ (j\ne s,\ j\to s),\qquad d_t(s,s)=-\frac{\sum_{i\ne s}P(i\mid s)d_t(s,i)}{P(s\mid s)},
--   $$
--   form a score rule for $P$ (Definition 4): they are computable from the comparisons observed at $s$, average to zero under $P(\cdot\mid s)$, satisfy $|d_t(s,j)|\le1$ off the diagonal and $|d_t(s,s)|\le2(1-P(s\mid s))$, and reproduce the Dirichlet form, $\sum_{i,j}p_iP_{ij}d_t(i,j)g_j=-\langle\ell_t,(I-P)g\rangle_p$.
--
--   This is where the tournament enters steering: scoring each pair from one endpoint suffices, by detailed balance.
--
--   Differences from the source: none.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Lemma 5, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_FeedbackSwitching_tScore

namespace FeedbackSwitching

/-- **Lemma 5 (One-sided scores reproduce the Dirichlet form)**, p.28 (PDF p.30). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Fix a tournament orientation. Let `P` be reversible with respect to a positive `p`, with
`P(s | s) ≥ 1/2` for every `s`. The scores in Eq. (21) form a score rule for `P`."

**Formalization Note.** `P` is a transition matrix (`P i j = P(j | i)`) and `p` a positive
probability vector (p.17: reversibility is defined for these). The scores of Eq. (21) depend on the
round only through its loss vector. -/
theorem lemma_5 {K : ℕ} (A : Fin K → Fin K → Prop) (hA : IsTournament A)
    (P : Matrix (Fin K) (Fin K) ℝ) (p : Fin K → ℝ) (hp : IsPosProbVec p)
    (hP : IsTransitionMatrix P) (hrev : IsReversible P p) (hhold : ∀ s, 1 / 2 ≤ P s s) :
    IsScoreRule A P p (fun _ ℓ s j => tScore A P ℓ s j) := by sorry

end FeedbackSwitching
