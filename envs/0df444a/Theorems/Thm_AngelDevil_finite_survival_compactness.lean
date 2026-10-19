-- Prove2me | Theorems.Thm_AngelDevil_finite_survival_compactness
-- name    : AngelDevil.finite_survival_compactness
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:36:53.692206+00:00
-- url     : https://prove2.me/theorems/9ce68653-543f-4f54-ad03-38a632ec30d1
-- title:
--   Finite-horizon survival yields an infinite winning strategy
-- statement:
--   For any nonnegative integer power, suppose that for every finite number n of rounds there exists an Angel strategy that remains safe for n rounds against every Devil. Then a single Angel strategy remains safe forever against every Devil. The finite strategies may depend on n; the conclusion uses one strategy for all rounds.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript p. 2, Claim 2.1 proof: the suitable limit of finite-horizon strategies.

import Definitions.Def_AngelDevil_FiniteHorizon
open AngelDevil

theorem AngelDevil.finite_survival_compactness (p : Nat)
    (hf : ∀ n, FiniteAngelWins p n) : AngelWins p := by sorry
