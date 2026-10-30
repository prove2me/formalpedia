-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_eq_A13_A14_net_payoffs_via_psi
-- name    : AnalystRanking.Revelation.eq_A13_A14_net_payoffs_via_psi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:44:34.296665+00:00
-- url     : https://prove2.me/theorems/fd7f9e51-1014-4c4a-8425-043e1c1c1ddd
-- title:
--   (A.13)–(A.14): net payoffs $\Delta U^h_i$, $\Delta U^l_i$ through $\Psi^h_i$, $\Psi^l_i$ with $\Lambda^h_i,\Lambda^l_i>0$
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Let the other analyst play $\sigma=(\sigma^h,\sigma^l)\in[0,1]^2$ and write $\chi=\rho\gamma(1-\gamma)$. Then
--   $$\Delta U^h_i(\sigma^h,\sigma^l,q)=\Lambda^h_i\Big[\frac{\Pr(H|h)}{\Pr(L|h)}-\Psi^h_i(\sigma^h,\sigma^l)\Big],\qquad \Delta U^l_i(\sigma^h,\sigma^l,q)=\Lambda^l_i\Big[-\frac{\Pr(H|l)}{\Pr(L|l)}+\Psi^l_i(\sigma^h,\sigma^l)\Big],$$
--   with $\Psi^h_i$, $\Psi^l_i$ of (A.11)–(A.12) evaluated at $\varphi$, and
--   $$\Lambda^h_i=\Pr(L|h)\,W_2\Big(\varphi-\big[\sigma^h(\gamma+\tfrac{\chi}{\gamma})+(1-\sigma^l)(1-\gamma-\tfrac{\chi}{\gamma})\big](\varphi-1)\Big)>0,$$
--   $$\Lambda^l_i=\Pr(L|l)\,W_2\Big(\varphi-\big[\sigma^h(\gamma-\tfrac{\chi}{1-\gamma})+(1-\sigma^l)(1-\gamma+\tfrac{\chi}{1-\gamma})\big](\varphi-1)\Big)>0,$$
--   where $W_2=w_0-w_2$, $\Pr(L|h)=(1-q)(1-\gamma)/\Pr(h)$ and $\Pr(L|l)=(1-q)\gamma/\Pr(l)$.
--
--   Here $\Delta U^h_i=U_i(\hat h|h)-U_i(\hat l|h)$ and $\Delta U^l_i=U_i(\hat l|l)-U_i(\hat h|l)$ are computed from the model's primitives. The identity shows that equilibrium behaviour depends on the payoffs only through $\varphi$, and reduces every best-response question to comparing posterior odds with $\Psi$.
--
--   Differences from the source:
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - encoding: Λh_i ≡ Pr(L|h)ΔU^{Hh}_i, Λl_i ≡ Pr(L|l)ΔU^{Hl}_i (A.9) with ΔU^{Hh}_i, ΔU^{Hl}_i of (A.10) → Λh, Λl written out from (A.9)–(A.10) with W1 − [·](W1 − W2) = W2(φ − [·](φ − 1)); reason: the same quantities, written in closed form
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.8a)–(A.10), p. 32, and (A.13)–(A.14), p. 33

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_dUh
import Definitions.Def_AnalystRanking_Revelation_dUl
import Definitions.Def_AnalystRanking_Revelation_psiH
import Definitions.Def_AnalystRanking_Revelation_psiL
import Definitions.Def_AnalystRanking_Revelation_oddsH
import Definitions.Def_AnalystRanking_Revelation_oddsL
import Definitions.Def_AnalystRanking_Revelation_phiConvexity
import Definitions.Def_AnalystRanking_Revelation_sigProbMarg

namespace AnalystRanking.Revelation

/-- **(A.13)–(A.14): the net payoffs in terms of `Ψʰ`, `Ψˡ`, with `Λʰ, Λˡ > 0`.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Appendix A, (A.8a)–(A.10), p. 32, and (A.13)–(A.14), p. 33:
`ΔUʰ_i(σʰ, σˡ, q) = Λʰ_i[Pr(H|h)/Pr(L|h) − Ψʰ_i(σʰ, σˡ)]` and
`ΔUˡ_i(σʰ, σˡ, q) = Λˡ_i[−Pr(H|l)/Pr(L|l) + Ψˡ_i(σʰ, σˡ)]`, "where by (A.9), `Λʰ_i, Λˡ_i > 0`",
with `Λʰ_i ≡ Pr(L|h) ΔU^{Hh}_i`, `Λˡ_i ≡ Pr(L|l) ΔU^{Hl}_i` (A.9) and, by (A.10),
`ΔU^{Hh}_i = W₁ − [σʰ(γ + χ/γ) + (1 − σˡ)(1 − γ − χ/γ)](W₁ − W₂)`,
`ΔU^{Hl}_i = W₁ − [σʰ(γ − χ/(1−γ)) + (1 − σˡ)(1 − γ + χ/(1−γ))](W₁ − W₂)`.

Here `Λʰ`, `Λˡ` are written out: `Pr(L|h) = (1 − q)(1 − γ)/Pr(h)`, `Pr(L|l) = (1 − q)γ/Pr(l)`, and
`W₁ − [·](W₁ − W₂) = W₂(φ − [·](φ − 1))`.

**Formalization Note.** `ΔUʰ`, `ΔUˡ` are computed from the primitives (`interimPay`), so this
statement is where the payoff triple reduces to `φ`. `σ` is the other analyst's strategy, in
`[0, 1]²`. -/
theorem eq_A13_A14_net_payoffs_via_psi (γ ρ q w1 w0 w2 : ℝ) (σ : ℝ × ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hw20 : w2 < w0) (hw01 : w0 < w1) (hσ1 : 0 ≤ σ.1) (hσ1' : σ.1 ≤ 1) (hσ2 : 0 ≤ σ.2) (hσ2' : σ.2 ≤ 1) :
    let φ := phiConvexity w1 w0 w2
    let χ := ρ * γ * (1 - γ)
    let Λh := (1 - q) * (1 - γ) / sigProbMarg q γ true * (w0 - w2) *
      (φ - (σ.1 * (γ + χ / γ) + (1 - σ.2) * (1 - γ - χ / γ)) * (φ - 1))
    let Λl := (1 - q) * γ / sigProbMarg q γ false * (w0 - w2) *
      (φ - (σ.1 * (γ - χ / (1 - γ)) + (1 - σ.2) * (1 - γ + χ / (1 - γ))) * (φ - 1))
    dUh w1 w0 w2 q γ ρ σ = Λh * (oddsH q γ - psiH γ ρ φ σ) ∧
      dUl w1 w0 w2 q γ ρ σ = Λl * (-oddsL q γ + psiL γ ρ φ σ) ∧ 0 < Λh ∧ 0 < Λl := by sorry

end AnalystRanking.Revelation
