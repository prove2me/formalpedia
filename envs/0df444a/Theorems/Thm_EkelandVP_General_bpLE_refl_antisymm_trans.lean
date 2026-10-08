-- Prove2me | Theorems.Thm_EkelandVP_General_bpLE_refl_antisymm_trans
-- name    : EkelandVP.General.bpLE_refl_antisymm_trans
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:48:24.776217+00:00
-- url     : https://prove2.me/theorems/592ddec2-6b74-4763-8e5b-f1a468aaa927
-- title:
--   §1, p. 325 — for $\alpha > 0$ the relation (1.6) is reflexive, antisymmetric and transitive
-- statement:
--   Let $(V,d)$ be a metric space, let $\alpha > 0$, and let $\prec$ be the relation (1.6) on $V\times\mathbb{R}$:
--   $(v_1,a_1)\prec(v_2,a_2)$ iff $(a_2-a_1)+\alpha\,d(v_1,v_2)\le 0$. Then $\prec$ is a partial order:
--
--   1. $p \prec p$ for every $p \in V\times\mathbb{R}$;
--   2. $p \prec q$ and $q \prec p$ imply $p = q$;
--   3. $p \prec q$ and $q \prec r$ imply $p \prec r$.
--
--   These three properties are what makes "maximal element" in Lemma 1.2 meaningful.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 325, §1, sentence after (1.6)

import Mathlib
import Definitions.Def_EkelandVP_General_bpLE

namespace EkelandVP.General

theorem bpLE_refl_antisymm_trans {V : Type*} [MetricSpace V] (α : ℝ) (hα : 0 < α) :
    (∀ p : V × ℝ, bpLE α p p) ∧
    (∀ p q : V × ℝ, bpLE α p q → bpLE α q p → p = q) ∧
    (∀ p q r : V × ℝ, bpLE α p q → bpLE α q r → bpLE α p r) := by sorry

end EkelandVP.General
