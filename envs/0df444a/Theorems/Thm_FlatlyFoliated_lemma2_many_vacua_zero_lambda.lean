-- Prove2me | Theorems.Thm_FlatlyFoliated_lemma2_many_vacua_zero_lambda
-- name    : FlatlyFoliated.lemma2_many_vacua_zero_lambda
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:43:46.777257+00:00
-- url     : https://prove2.me/theorems/a6f912ac-546d-4a4e-9248-660f120035ac
-- title:
--   Lemma 2 — $\Lambda=0$: many vacuum solutions spherically symmetric at infinity
-- statement:
--   For $\Lambda=0$ there is a sequence $(\omega_n,\eta_n)_{n\in\mathbb N}$ of smooth vacuum solutions of the FFR equations (34)–(35) (with $\mu=0$, $J=0$) such that every $\eta_n>0$, every $(\omega_n,\eta_n)$ is spherically symmetric at infinity, and no two distinct members are related by an overall positive constant: for $m\ne n$ there is no $c>0$ with $(\omega_m,\eta_m)=c\,(\omega_n,\eta_n)$.
--
--   So uniqueness of the vacuum, up to rescaling of $t$, fails when $\Lambda=0$.
--
--   **Formalization Note** "Many" is formalized as infinitely many pairwise inequivalent solutions.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 20, Lemma 2 (eqs. (103)–(108))

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Lemma 2: for `Λ = 0` there are many (here: infinitely many, pairwise not related by a
positive rescaling) smooth vacuum solutions that are spherically symmetric at infinity. -/
theorem lemma2_many_vacua_zero_lambda :
    ∃ sol : ℕ → (R3 → R3) × (R3 → ℝ),
      (∀ n, ContDiff ℝ ∞ (sol n).1 ∧ ContDiff ℝ ∞ (sol n).2 ∧ (∀ x, 0 < (sol n).2 x) ∧
        FFREquations 0 0 0 (sol n).1 (sol n).2 ∧ SphSymmAtInfty (sol n).1 (sol n).2) ∧
      ∀ m n, m ≠ n → ¬ ∃ c : ℝ, 0 < c ∧ (sol m).1 = c • (sol n).1 ∧ (sol m).2 = c • (sol n).2 := by sorry

end FlatlyFoliated
