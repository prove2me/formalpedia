-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_3_5
-- name    : DictatorsCK.Main.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:12.025194+00:00
-- url     : https://prove2.me/theorems/f3921c7b-bdb2-4217-a1e3-109d6ff9beda
-- title:
--   Lemma 3.5 — a nonnegative $M_{\rho_0}(a)$ propagates to every smaller $\rho$, with $M_\rho(a)/\rho^2\ge M_{\rho_0}(a)/\rho_0^2$
-- statement:
--   Let $M_\rho(a)=(1-\rho^2)H(\rho a)-(1-\rho^2a)H(\rho)$ with $H(t)=H_b((1-t)/2)$ in nats. Fix $a\in[0,1]$. If $M_{\rho_0}(a)\ge0$ at some $0<\rho_0<1$, then for every $0<\rho\le\rho_0$
--   $$\frac{M_\rho(a)}{\rho^2}\ge\frac{M_{\rho_0}(a)}{\rho_0^2}\ge0,$$
--   and in particular $M_\rho(a)\ge0$ for every $0\le\rho\le\rho_0$.
--
--   Together with the concavity in Theorem 3.4, one numerical check $M_{\rho_0}(a_0)\ge0$ covers every smaller correlation and every larger singleton coefficient.
--
--   Differences from the source: none.
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 14 (PDF 15), Lemma 3.5

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_3_5 (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ρ₀ : ℝ) (hρ₀0 : 0 < ρ₀) (hρ₀1 : ρ₀ < 1)
    (hM : 0 ≤ Mfun ρ₀ a) :
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Mfun ρ₀ a / ρ₀ ^ 2 ≤ Mfun ρ a / ρ ^ 2) ∧
    0 ≤ Mfun ρ₀ a / ρ₀ ^ 2 ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρ₀ → 0 ≤ Mfun ρ a) := by sorry

end DictatorsCK.Main
