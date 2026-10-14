-- Prove2me | Theorems.Thm_FakeAccounts_Platform_d1_lt_d2
-- name    : FakeAccounts.Platform.d1_lt_d2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:40.742336+00:00
-- url     : https://prove2.me/theorems/e3ab674f-ddb6-45e6-8a8c-c2abf2544825
-- title:
--   (18), p. 8872 — the pooling threshold d₁ is strictly below the separating threshold d₂
-- statement:
--   Under the standing parameter ranges of the model, the antifake-effort threshold up to which pooling is sustainable lies strictly below the threshold up to which costly separation is sustainable:
--   $$d_1=(1-\tau)(\eta_1-p_0)\;<\;(1-\tau)(\eta_2-p_0)=d_2,$$
--   with $\eta_1=\lambda_i\mu(1-l)\big[q_H(E[q]-q_L)/(lE[q](q_H-q_L))+\rho\big]$ and $\eta_2=\frac1l\lambda_i\mu(1-l^2)$.
--
--   This ordering makes the three regions of Proposition 1 (pooling, costly separating, naturally separating) appear in that order as $d$ grows.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8872, (13), (16), (18)

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- (18), p. 8872: the pooling threshold d₁ lies strictly below the separating threshold d₂. -/
theorem d1_lt_d2 (P : Params) (hP : Standing P) : d1 P < d2 P := by sorry

end FakeAccounts.Platform
