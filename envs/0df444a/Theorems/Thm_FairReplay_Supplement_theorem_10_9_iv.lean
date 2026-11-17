-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_9_iv
-- name    : FairReplay.Supplement.theorem_10_9_iv
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:01:13.076205+00:00
-- url     : https://prove2.me/theorems/52236521-c678-4f29-8283-cb904ddaf8fe
-- title:
--   Theorem 10.9(iv) — $Q_{\mathrm{LB}}(d)=\frac a{b_2}\big(\sum_{x\in U}\bar c_x\big)d^{-2}+a\big(C^{A\setminus U}_{\mathrm{ctrl}}-\frac{b_3}{b_2^2}\sum_{x\in U}\bar c_x\big)d^{-1}+O(1)$
-- statement:
--   Fix a declared two-class family in which every candidate is observable, $p,s,\tau>0$ with $p+s+\tau<1$, $r=1-p-s-\tau$, $\delta\in(0,1/2)$ and $a=\mathrm{kl}(1-\delta,\delta)$. Let $U=\{x\in A:C_{x,i}=0\ \forall i\}$, $b_2=\frac12(\tau^{-1}+r^{-1})$, $b_3=\frac13(r^{-2}-\tau^{-2})$, $\bar c_x=\min\{c_i:x\in S_i\}$, and
--   $$C^{A\setminus U}_{\mathrm{ctrl}}=\min_{q\ge0}\big\{c^\top q:\ C_{A\setminus U}\,q\ge\mathbf 1\big\}\quad(\text{zero if }A\setminus U=\varnothing).$$
--   Then $C^{A\setminus U}_{\mathrm{ctrl}}$ is finite and, as $d\downarrow0$, the value of the lower program of (i) satisfies
--   $$Q_{\mathrm{LB}}(d)=\frac{a}{b_2}\Big(\sum_{x\in U}\bar c_x\Big)d^{-2}+a\Big(C^{A\setminus U}_{\mathrm{ctrl}}-\frac{b_3}{b_2^2}\sum_{x\in U}\bar c_x\Big)d^{-1}+O(1).$$
--
--   This is an exact asymptotic for the information lower program, not a matching upper bound when $U\neq\varnothing$.
--
--   Differences from the source:
--   - encoding: + O(1) as d ↓ 0 → ∃ C, d₀ > 0 chosen before d with |QLB(d) − main terms| ≤ C on (0, d₀); reason: standard
--   - encoding: QLB(d) and C^{A∖U}_ctrl as real numbers → values in [0, ∞] with explicit finiteness conjuncts, compared through toReal; reason: the finiteness conjuncts exclude the ∞ junk value
--   - encoding: the declared two-class family (vertices low/high, candidates A, legal groups S_i with |S_i| ≥ 2, costs c_i > 0) → a TwoClassFamily structure on Fin n whose first k actions query the k groups and whose final deterministic zero-cost action represents making no query; a query of S_i reveals the coded ordered old/new outputs of its members on one fresh tape; reason: direct transcription of §10.5; the idle action carries no information and keeps the zero-query tester expressible when k = 0; coordinates outside S_i are constant
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(iv), eqs. (69)–(71), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_armCount
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Qstar0
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_Bcap

open MeasureTheory

namespace FairReplay.Supplement

open TwoClassFamily

/-- **Theorem 10.9(iv), the two-term expansion of the lower program, eqs. (69)–(71)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem
10.9(iv), p.19 (PDF p.21)): "(iv) The mixed-topology information floor has an exact two-term singular
expansion. Let U = {x ∈ A : Cxi = 0 ∀i}, b2 = 1/2 (τ−1 + r−1), b3 = 1/3 (r−2 − τ−2). (69) and, for each
observable x ∈ U, let c̄x = min{ci : x ∈ Si}. Write C^{A\U}_ctrl = min_{q≥0} { c⊤q : C_{A\U} q ≥ 1 }, (70)
with value zero if A \ U is empty, and let a = kl(1 − δ, δ). If every candidate is observable, then as
d ↓ 0 the value QLB(d) of the lower program in (i) satisfies QLB(d) = a/b2 (Σ_{x∈U} c̄x) d−2 +
a (C^{A\U}_ctrl − b3/b2² Σ_{x∈U} c̄x) d−1 + O(1). (71)"

For a declared two-class family `F`, fixed `p, s, τ > 0` with `p + s + τ < 1` and `δ ∈ (0, 1/2)`, in which every
candidate lies in some legal group: `C^{A∖U}_ctrl` is finite, and there are `C, d₀ > 0` such that for every
`d ∈ (0, d₀)` the lower program `QLB(d)` of (i) is finite and
`|QLB(d) − (a/b2 · Σ_{x∈U} c̄_x · d⁻² + a (C^{A∖U}_ctrl − (b3/b2²) Σ_{x∈U} c̄_x) d⁻¹)| ≤ C`,
where `U` is the set of unmatched candidates, `a = kl(1 − δ, δ)`, `b2 = (τ⁻¹ + r⁻¹)/2`, `b3 = (r⁻² − τ⁻²)/3`,
`r = 1 − p − s − τ`.

**Formalization Note** `O(1)` as `d ↓ 0` is written with explicit constants `C, d₀` chosen before `d`.
`C^{A∖U}_ctrl` is `coverLP` on the rows `A ∖ U`, which is `0` when `A ∖ U = ∅`. The finiteness conjuncts
make the real-valued comparison meaningful. -/
theorem theorem_10_9_iv (F : TwoClassFamily) (p s τ δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hτ : 0 < τ)
    (hpst : p + s + τ < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) (hobs : ∀ x ∈ F.A, F.Observable x) :
    F.coverLP (F.A \ F.unmatched) ≠ ⊤ ∧
    ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s - τ ∧
      ∀ d, 0 < d → d < d₀ → F.QLB p s τ d δ ≠ ⊤ ∧
        |(F.QLB p s τ d δ).toReal -
          (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ / b2 p s τ *
              (∑ x ∈ F.unmatched, F.cbar x) * (d ^ 2)⁻¹ +
            BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ *
              ((F.coverLP (F.A \ F.unmatched)).toReal -
                b3 p s τ / b2 p s τ ^ 2 * ∑ x ∈ F.unmatched, F.cbar x) * d⁻¹)| ≤ C := by sorry

end FairReplay.Supplement
