-- Prove2me | Theorems.Thm_EkelandVP_General_lemma_1_2
-- name    : EkelandVP.General.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:48:44.906304+00:00
-- url     : https://prove2.me/theorems/38175098-5424-417b-a3e0-12154117a5d7
-- title:
--   Lemma 1.2, p. 325 — a closed subset of $V\times\mathbb{R}$ bounded below in $a$ has a maximal element above each of its points
-- statement:
--   Let $(V,d)$ be a complete metric space, let $\alpha>0$, and let $\prec$ be the order (1.6) on $V\times\mathbb{R}$. Let $S\subseteq V\times\mathbb{R}$ be closed and bounded below in the second coordinate:
--
--   $$
--   \exists\, m\in\mathbb{R}:\quad (v,a)\in S \;\Rightarrow\; a \ge m. \tag{1.7}
--   $$
--
--   Then for every $(v_1,a_1)\in S$ there is $(\bar v,\bar a)\in S$ with $(v_1,a_1)\prec(\bar v,\bar a)$ which is maximal in $S$ for $\prec$: every $(v,a)\in S$ with $(\bar v,\bar a)\prec(v,a)$ equals $(\bar v,\bar a)$.
--
--   No compactness is assumed; completeness of $V$ replaces it. Theorem 1.1 is this lemma applied to the epigraph of $F$ with $\alpha=\varepsilon/\lambda$.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 325, Lemma 1.2, (1.7)

import Mathlib
import Definitions.Def_EkelandVP_General_bpLE

namespace EkelandVP.General

theorem lemma_1_2 {V : Type*} [MetricSpace V] [CompleteSpace V] (α : ℝ) (hα : 0 < α)
    (S : Set (V × ℝ)) (hS : IsClosed S) (hm : ∃ m : ℝ, ∀ p ∈ S, m ≤ p.2)
    (p₁ : V × ℝ) (hp₁ : p₁ ∈ S) :
    ∃ q ∈ S, bpLE α p₁ q ∧ ∀ r ∈ S, bpLE α q r → r = q := by sorry

end EkelandVP.General
