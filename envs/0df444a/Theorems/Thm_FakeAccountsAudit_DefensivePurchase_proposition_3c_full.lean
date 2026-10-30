-- Prove2me | Theorems.Thm_FakeAccountsAudit_DefensivePurchase_proposition_3c_full
-- name    : FakeAccountsAudit.DefensivePurchase.proposition_3c_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:45:13.395024+00:00
-- url     : https://prove2.me/theorems/1090f26f-f3f2-4523-97b3-de8ff24e27aa
-- title:
--   Proposition 3(c) — both effort-shape cases, including zero costs
-- statement:
--   Consider a unit mass of consumers and two influencer qualities $0<q_L<q_H$. Let $\mu>0$ be advertising revenue per real consumer, $0<\lambda_i<1$ the influencer's share, $0<l<1$ social media literacy, $0\le\tau<1$ the technology level, $p_0>0$ the base fake-account price, and $c_0,c_1\ge0$ the cost coefficients. For real effort $d\ge0$, write
--
--   $$p_f(d)=p_0+\frac{d}{1-\tau},\qquad c(d)=c_0+c_1(1-\tau)d.$$
--
--   Under separation, the informed and uninformed follower masses for quality $q_t$ are $n_{in}^t(d)=l(1-c(d)/q_t)$ and $n_{un}^t(d)=(1-l)(1-c(d)/q_t)$. Compute the H-type's early-follower count by equation (17):
--
--   $$n_2^{csep}(d)=\frac{\lambda_i\mu}{p_f(d)}\big[(1-l)(n_{in}^H(d)-n_{in}^L(d))+(n_{un}^H(d)-n_{un}^L(d))\big]+n_{in}^L(d).$$
--
--   The defensive purchase is the computed quantity $x(d)=n_2^{csep}(d)-n_{in}^H(d)$. Set
--
--   $$A=\lambda_i\mu(1-l^2),\quad \eta_2=A/l,\quad d_2=(1-\tau)(\eta_2-p_0),\quad I=[0,d_2],$$
--   $$K=c_1(1-\tau)^2,\qquad T=\frac{A c_0}{p_0(A-p_0l)}.$$
--
--   Assume the paper's Assumption 3, $p_0<\eta_2$. Thus $d_2>0$ and the denominator defining $T$ is positive. All of the following hold:
--
--   1. Under the exact condition (22), $K\le T$, purchase is nonincreasing on $I$. If additionally $c_0+c_1>0$, it is strictly decreasing on $I$, including when $K=T$.
--   2. If $c_0=c_1=0$, then $x(d)=0$ for every $d\in I$.
--   3. If (22) fails, $T<K$, there is an $h$ with
--
--   $$0<h<d_2,\qquad x\text{ strictly increasing on }[0,h],\qquad x\text{ strictly decreasing on }[h,d_2].$$
--
--   In particular the third conclusion covers $c_0=0<c_1$. Both ends of each interval are included. This states both shape conclusions of Proposition 3(c), with the strict positive-cost behavior and its precise flat degeneracy in one item.
--
--   The physical game also assumes $q_L>c(d)$ (Assumption 1) and $\lambda_i>p_f(d)/(\mu+p_f(d))$ (Assumption 2). The theorem analytically extends the explicit conditional branch to all of $I$; its equilibrium interpretation applies on the intersection with these conditions. Proposition 1 selects that branch globally on $I$ if $d_1\le0$, and on $(d_1,d_2]$ if $d_1>0$, again intersected with Assumptions 1–2. Here $E[q]=\rho q_H+(1-\rho)q_L$, $\eta_1=\lambda_i\mu(1-l)[q_H(E[q]-q_L)/(lE[q](q_H-q_L))+\rho]$ and $d_1=(1-\tau)(\eta_1-p_0)$. The peak need not lie above $d_1$. No claim of positive-purchase equilibrium existence is made at zero-cost or zero-purchase degeneracies or outside the physical conditions.
--
--   **Formalization Note.** The published raw parameters and follower formulas add no hypotheses. The goal does not assume their bundled `Standing` predicate, a desired derivative sign, an identity for an arbitrary function, or a preselected peak. Coordinates $\rho,\lambda_p,\gamma$ are unrestricted because the purchase does not depend on them. The exact source price and cost slopes, rather than an assumed monotonicity property, determine $x$.
--
--
--   Differences from the source:
--   - reading: under the costly separating equilibrium → the conditional locally costly separating branch on the whole closed interval [0,d₂], without requiring the peak to exceed d₁; reason: the globally selected branch may start after the peak; this reading retains both shape conclusions and restricts to every globally selected source point
--   - reading: decreases, without a weak or strict qualifier → nonincrease under (22), strict decrease when c₀+c₁>0, and the exact zero identity when c₀=c₁=0; reason: the positive-cost strict result includes equality in (22); zero costs make the computed purchase identically zero, so unconditional strictness is false
--   - generalization: efforts satisfying Assumptions 1–2 and supporting a costly separating equilibrium → the computed branch on all of [0,d₂], including its zero-cost and zero-purchase boundary extension; reason: the algebraic claim holds beyond q_L>c(d) and λ_i>p_f(d)/(μ+p_f(d)); restriction to their intersection recovers all source-admissible comparisons without claiming PBE existence outside it
--   - generalization: the full game also restricts ρ, λ_p, λ_a and γ → raw parameter records with no restrictions on ρ, λ_p or γ; reason: these coordinates do not occur in price, cost, n₂ from (17), the computed purchase, or the threshold; all source records remain covered
--   - encoding: unit consumer mass, continuous effort and follower quantities, and source quotients → real variables, closed intervals and explicit 0<l<1, 0<p₀ and 0<q_L<q_H; reason: these encode the source-defined quotient domain; Assumption 1 with nonnegative costs implies positive q_L, l=0 is undefined and l=1 contradicts Assumption 3
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(c) and condition (22), PDF page 12; §3, pp. 8868–8870 (PDF 5–7), Assumptions 1–2; §4.2.2, p. 8872 (PDF 9), equations (16)–(20); Assumption 3 and Proposition 1, p. 8873 (PDF 10); DOI:10.1287/mnsc.2022.02616

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting
set_option autoImplicit false

namespace FakeAccountsAudit.DefensivePurchase

/-- Huang--Liu, p. 8875 (PDF 12), Proposition 3(c), exact (22).
The explicit (17) purchase branch is considered on the full local interval [0,d₂].
This analytically extends beyond effort-dependent Assumptions 1--2 and leaves
irrelevant coordinates unrestricted; it does not assert PBE existence there.
"Decreases" is strict for nonzero nonnegative costs and weak in the zero-cost
extension, where the purchase is identically zero. Equality in (22) belongs to
the decreasing case. No condition puts the peak above the global threshold d₁. -/
theorem proposition_3c_full (P : FakeAccounts.Platform.Params)
    (hmu : 0 < P.mu) (hlamI : 0 < P.lamI) (hlamI_one : P.lamI < 1)
    (hl : 0 < P.l) (hl_one : P.l < 1)
    (hqL : 0 < P.qL) (hq : P.qL < P.qH)
    (hc0 : 0 ≤ P.c0) (hc1 : 0 ≤ P.c1)
    (htau : 0 ≤ P.tau) (htau_one : P.tau < 1)
    (hp0 : 0 < P.p0) (hA3 : P.p0 < FakeAccounts.Platform.eta2 P) :
    (P.c1 * (1 - P.tau) ^ 2 ≤
        P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
          (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) →
      AntitoneOn (FakeAccounts.Defensive.xCsepH P) (Set.Icc 0 (FakeAccounts.Platform.d2 P)) ∧
        (0 < P.c0 + P.c1 →
          StrictAntiOn (FakeAccounts.Defensive.xCsepH P)
            (Set.Icc 0 (FakeAccounts.Platform.d2 P)))) ∧
    (P.c0 = 0 → P.c1 = 0 →
      ∀ d ∈ Set.Icc 0 (FakeAccounts.Platform.d2 P),
        FakeAccounts.Defensive.xCsepH P d = 0) ∧
    (P.lamI * P.mu * (1 - P.l ^ 2) * P.c0 /
        (P.p0 * (P.lamI * P.mu * (1 - P.l ^ 2) - P.p0 * P.l)) <
          P.c1 * (1 - P.tau) ^ 2 →
      ∃ h : ℝ, 0 < h ∧ h < FakeAccounts.Platform.d2 P ∧
        StrictMonoOn (FakeAccounts.Defensive.xCsepH P) (Set.Icc 0 h) ∧
        StrictAntiOn (FakeAccounts.Defensive.xCsepH P)
          (Set.Icc h (FakeAccounts.Platform.d2 P))) := by sorry

end FakeAccountsAudit.DefensivePurchase
