-- Prove2me | Theorems.Thm_DraftPoA_instance_facts
-- name    : DraftPoA.instance_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:20.295147+00:00
-- url     : https://prove2.me/theorems/0e5c10c1-03c0-4f33-86f5-14a3a8f06dc6
-- title:
--   Facts about the lower-bound instance: rounding, ordering, $w<h<\sigma_N$, $\ln K+3\le wr\le\ln K+3.05$, $\mathrm{OPT}$
-- statement:
--   Let $N\ge4$, $K=\lceil H_N\rceil$, $\delta=\delta_N=1/(4N^2K^2)$, and let $\alpha_j,\sigma_j,\varphi_j,w,h,r,m(N)$ be the parameters of the instance (any number $d$ of dummy items). Then:
--
--   1. $3\le K\le H_N+1$;
--   2. for every integer $j\ge1$: $1/j-\delta<\alpha_j\le1/j$ and $1/(jK)-\delta<\sigma_j\le1/(jK)$; and $\sigma_N=1/(NK)$ exactly;
--   3. for $1\le j<N$: $\alpha_{j+1}<\alpha_j$, $\sigma_{j+1}<\sigma_j$, $\varphi_{j+1}<\varphi_j$;
--   4. for every sink item $j$: $\sigma_j<\varphi_j<\alpha_j$;
--   5. $w<h<1/(NK)=\sigma_N\le\sigma_j$ for every sink item $j$;
--   6. $\ln K+3\le wr\le\ln K+3.05$;
--   7. $m(N)\le N+2NK(\ln K+3)+1$;
--   8. $\mathrm{OPT}=\sum_{j=1}^N\alpha_j+hr>H_N-N\delta+hr$.
--
--   These are the numerical facts behind the welfare bound and the one-shot checks of Appendix B.
--
--   Differences from the source:
--   - generalization: rounding bounds "for every j" (sink items) → for every natural number j ≥ 1; reason: rounding down loses less than δ for every j
--   - generalization: OPT of the instance with m(N) items → OPT for every number d of dummy items; reason: dummy items are worth 0 to everybody; d = 0 is the source's case
--   - reading: OPT is at least H_N − Nδ + hr (p.21) → OPT > H_N − Nδ + hr; reason: §4.3, p.10 prints the strict inequality
--   - reading: α_j, σ_j, φ_j decrease strictly in j; σ_j < φ_j < α_j for every j → for sink items, 1 ≤ j < N resp. 1 ≤ j ≤ N; reason: j indexes the sink items; the proof uses j ≤ N
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), App. B "Facts about the instance", pp.20–21 (PDF 21–22); §4.3, p.10 (PDF 11)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Facts about the instance, App. B, pp.20–21 (PDF 21–22) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4` (and any number `d` of dummy items): `3 ≤ K ≤ H_N + 1`; rounding
`1/j − δ < α_j ≤ 1/j`, `1/(jK) − δ < σ_j ≤ 1/(jK)` for every `j ≥ 1`, and `σ_N = 1/(NK)` exactly;
`α_j`, `σ_j`, `φ_j` decrease strictly in `j` (for `j < N`); `σ_j < φ_j < α_j` for every sink item;
`w < h < 1/(NK) = σ_N ≤ σ_j`; `ln K + 3 ≤ wr ≤ ln K + 3.05`; `m ≤ N + 2NK(ln K + 3) + 1`; and
`OPT = Σ_j α_j + hr > H_N − Nδ + hr`.

**Formalization Note.** `δ` here is the value-rounding increment `δ_N = deltaOf N`. The number of
items is `m(N) = mOf N`; with `d` dummy items `OPT` is unchanged, as dummy items are worth `0`. -/
theorem instance_facts (N : ℕ) (hN : 4 ≤ N) (d : ℕ) :
    3 ≤ Kof N ∧ (Kof N : ℝ) ≤ (harmonic N : ℝ) + 1 ∧
    (∀ j : ℕ, 1 ≤ j →
      1 / (j : ℝ) - deltaOf N < alpha N j ∧ alpha N j ≤ 1 / (j : ℝ) ∧
      1 / ((j : ℝ) * Kof N) - deltaOf N < sigma N j ∧ sigma N j ≤ 1 / ((j : ℝ) * Kof N)) ∧
    sigma N N = 1 / ((N : ℝ) * Kof N) ∧
    (∀ j : ℕ, 1 ≤ j → j < N →
      alpha N (j + 1) < alpha N j ∧ sigma N (j + 1) < sigma N j ∧ phi N (j + 1) < phi N j) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ N → sigma N j < phi N j ∧ phi N j < alpha N j) ∧
    wOf N < hOf N ∧ hOf N < 1 / ((N : ℝ) * Kof N) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ N → sigma N N ≤ sigma N j) ∧
    Real.log (Kof N) + 3 ≤ wOf N * rOf N ∧ wOf N * rOf N ≤ Real.log (Kof N) + 3.05 ∧
    (mOf N : ℝ) ≤ N + 2 * N * Kof N * (Real.log (Kof N) + 3) + 1 ∧
    OPT (vBad N d) = ∑ j ∈ Finset.Icc 1 N, alpha N j + hOf N * rOf N ∧
    (harmonic N : ℝ) - N * deltaOf N + hOf N * rOf N < OPT (vBad N d) := by sorry

end DraftPoA
