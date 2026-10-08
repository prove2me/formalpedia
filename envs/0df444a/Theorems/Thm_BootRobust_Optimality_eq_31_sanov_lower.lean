-- Prove2me | Theorems.Thm_BootRobust_Optimality_eq_31_sanov_lower
-- name    : BootRobust.Optimality.eq_31_sanov_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:38.873125+00:00
-- url     : https://prove2.me/theorems/7695d32b-b601-41f5-88c8-0ff59eaaf4a0
-- title:
--   (31), p. 16 — Sanov's lower bound: −inf_{int 𝒞} B(D, D_tr) ≤ liminf (1/n) log D^∞_tr[D_bs[n] ∈ 𝒞]
-- statement:
--   Let $D_{\rm tr}\in\mathcal D_n$ have all coordinates positive, let $\mathcal C\subseteq\mathbb R^\iota$ be any set, and let $D\in\mathcal D_n$ lie in the interior of $\mathcal C$ relative to $\mathcal D_n$. Then for every $\varepsilon>0$, for all sufficiently large $n$,
--   $$D_{\rm tr}^n\big[D_{{\rm bs}[n]}\in\mathcal C\big]\ \ge\ \exp\!\big(-n\,(B(D,D_{\rm tr})+\varepsilon)\big),$$
--   where $D_{\rm tr}^n$ is the law of $n$ independent draws from $D_{\rm tr}$ and $D_{{\rm bs}[n]}$ is their empirical distribution.
--
--   Holding for every $D\in{\rm int}\,\mathcal C$ and every $\varepsilon$, this is Sanov's lower bound (31) on a finite alphabet:
--   $$-\inf_{D\in{\rm int}\,\mathcal C}B(D,D_{\rm tr})\le\liminf_{n\to\infty}\frac1n\log D^\infty_{\rm tr}\big[D_{{\rm bs}[n]}\in\mathcal C\big].$$
--   It shows that the bootstrap inequality of Theorem 6 is exact in the exponential rate.
--
--   **Formalization Note** The pointwise form with an explicit $\varepsilon$ is equivalent to (31) and avoids $\log 0$. Since $D_{\rm tr}>0$, $B(D,D_{\rm tr})$ is finite and is used as a real number. Only the first $n$ coordinates of the infinite bootstrap process enter the event, so its law is the $n$-fold product. Full support of $D_{\rm tr}$ is the paper's convention that $\Omega_n$ is the support of the training data.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, (31), p. 16 (citing Dembo and Zeitouni 2009, Theorem 6.2.10)

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting

namespace BootRobust.Optimality

open MeasureTheory

/-- Sanov's lower bound, Eq. (31), p. 16, in pointwise form: for every set `C`, every `D` in the
interior of `C` relative to `𝒟ₙ` and every `ε > 0`, eventually in `n`,
`Dⁿ_tr(D_bs[n] ∈ C) ≥ exp(-n (B(D, D_tr) + ε))`. Over all such `D` this is
`-inf_{D ∈ int C} B(D, D_tr) ≤ liminf (1/n) log D^∞_tr[D_bs[n] ∈ C]`. The training distribution has
full support, so `B(D, D_tr)` is finite and `EReal.toReal` returns its value. -/
theorem eq_31_sanov_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Dtr : ι → ℝ) (hDtr : Dtr ∈ stdSimplex ℝ ι) (hDtrpos : ∀ i, 0 < Dtr i)
    (C : Set (ι → ℝ)) (D : ι → ℝ) (hDC : D ∈ relInt C) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ((BootRobust.Perf.bootDist D Dtr).toReal + ε)))) ≤
        bootLaw Dtr n {ω | empDist ω ∈ C} := by sorry

end BootRobust.Optimality
