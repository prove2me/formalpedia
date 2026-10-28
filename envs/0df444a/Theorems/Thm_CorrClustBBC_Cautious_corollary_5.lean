-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_corollary_5
-- name    : CorrClustBBC.Cautious.corollary_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:27.939994+00:00
-- url     : https://prove2.me/theorems/985b75b6-cd6b-4863-8871-d0375da662a4
-- title:
--   Corollary 5, p. 96 — a clustering whose clusters are all δ-clean (δ ≤ 1/4) makes at most 4·m_OPT mistakes
-- statement:
--   Let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$, let $\delta\le 1/4$ be real, and let $D$ be a clustering of $V$ in which every cluster is $\delta$-clean. Then for every clustering $D'$ of $V$,
--   $$m_D\ \le\ 4\,m_{D'} ,$$
--   that is, $m_D\le 4\,m_{\mathrm{OPT}}$.
--
--   Clean clusterings are therefore $4$-approximations; the corollary is the paper's summary of Lemmas 3 and 4.
--
--   Differences from the source:
--   - encoding: m_D ≤ 4·m_OPT → m_D ≤ 4·m_{D′} for every clustering D′; reason: m_OPT is the minimum of m_{D′} over all clusterings, so the two statements are equivalent.
--   - encoding: a clustering of V → a setoid on V, its clusters being the classes; reason: a clustering is a partition, and partitions are setoids.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 96, Corollary 5

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem corollary_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (δ : ℝ) (hδ : δ ≤ 1 / 4) (D : Setoid V)
    (hD : ∀ v, IsClean G Finset.univ δ (classOf D v)) (D' : Setoid V) :
    mistakes G D.r ≤ 4 * mistakes G D'.r := by sorry
end CorrClustBBC.Cautious
