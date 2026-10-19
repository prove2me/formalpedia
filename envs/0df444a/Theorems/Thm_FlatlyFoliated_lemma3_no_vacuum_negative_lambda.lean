-- Prove2me | Theorems.Thm_FlatlyFoliated_lemma3_no_vacuum_negative_lambda
-- name    : FlatlyFoliated.lemma3_no_vacuum_negative_lambda
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:44:25.876139+00:00
-- url     : https://prove2.me/theorems/0b7ad3b1-7433-45c0-8404-aff11b1e65e5
-- title:
--   Lemma 3 — $\Lambda<0$: no vacuum solution spherically symmetric at infinity
-- statement:
--   Let $\Lambda<0$. There is no pair of smooth fields $(\omega,\eta)$ on $\mathbb R^3$ with $\eta>0$ that solves the vacuum FFR equations (34)–(35) (with $\mu=0$, $J=0$) and is spherically symmetric at infinity.
--
--   So existence fails when $\Lambda<0$.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 20, Lemma 3 (eqs. (109)–(115))

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Lemma 3: for `Λ < 0` there is no smooth vacuum solution with `η > 0` that is spherically
symmetric at infinity. -/
theorem lemma3_no_vacuum_negative_lambda (Λ : ℝ) (hΛ : Λ < 0) :
    ¬ ∃ (w : R3 → R3) (η : R3 → ℝ), ContDiff ℝ ∞ w ∧ ContDiff ℝ ∞ η ∧ (∀ x, 0 < η x) ∧
      FFREquations Λ 0 0 w η ∧ SphSymmAtInfty w η := by sorry

end FlatlyFoliated
