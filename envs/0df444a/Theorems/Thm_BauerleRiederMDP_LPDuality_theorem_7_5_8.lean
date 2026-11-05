-- Prove2me | Theorems.Thm_BauerleRiederMDP_LPDuality_theorem_7_5_8
-- name    : BauerleRiederMDP.LPDuality.theorem_7_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:29:19.358254+00:00
-- url     : https://prove2.me/theorems/28de89d4-4249-41ae-95c7-4db7aa7a6a1f
-- title:
--   Theorem 7.5.8 (Strong duality) — (P) and (D) have optimal solutions and equal values $\int J_\infty\,dp$
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a contracting Markov Decision Model with a bounding function $b:E\to\mathbb R_+$, i.e. there are $c_r,\alpha_b\ge0$ with $|r(x,a)|\le c_rb(x)$ and $\int b(x')Q(dx'\mid x,a)\le\alpha_bb(x)$ for $(x,a)\in D$, and $\beta\alpha_b<1$. Assume $b(x)\ge1$ for all $x$ and $\int b\,dp<\infty$. Let $I\!M$ be a closed linear subspace of $\mathbb B_b$ (the measurable $v$ with $\|v\|_b<\infty$) with $b\in I\!M$, and consider the linear programs
--   $$
--   (P)\quad \int v\,dp\to\min,\quad v(x)-\beta\int v(x')Q(dx'\mid x,a)\ge r(x,a),\ (x,a)\in D,\quad v\in I\!M,
--   $$
--   $$
--   (D)\quad \int r\,d\mu\to\max,\quad \int\Big(v(x)-\beta\int v(x')Q(dx'\mid x,a)\Big)\mu(d(x,a))=\int v\,dp\ \ \forall v\in I\!M,\quad \mu\in\mathcal M_b,
--   $$
--   where $\mathcal M_b$ is the set of measures $\mu$ on $D$ with $\int b\,d\mu<\infty$. Let $\mathrm{val}(P)$ and $\mathrm{val}(D)$ be the infimum of (P) and the supremum of (D).
--
--   Suppose the assumptions of Theorem 7.3.5 hold for $I\!M$: the maximal reward operator maps $I\!M$ into $I\!M$, and every $v\in I\!M$ has a maximizer $f\in\Delta$ for a given set $\Delta\subset F$ of decision rules. Then:
--
--   1. (P) has an optimal solution $v^*\in I\!M$, $v^*=J_\infty$, and
--   $$
--   \mathrm{val}(P)=\int J_\infty(x)\,p(dx)=\mathrm{val}(D).
--   $$
--   2. (D) has an optimal solution $\mu^*\in\mathcal M_b$, and there is a decision rule $f^*\in F$ with
--   $$
--   \mathrm{val}(D)=\int r\,d\mu^*=\int J_{f^*}(x)\,p(dx).
--   $$
--   In particular the stationary policy $(f^*,f^*,\dots)$ is $p$-optimal: it maximizes $\pi\mapsto\int J_{\infty\pi}\,dp$ over all Markov policies.
--
--   Strong duality turns the infinite-horizon problem into a pair of linear programs: the value function is the optimal solution of the primal, and the occupation measure of an optimal stationary policy solves the dual.
--
--   **Formalization Note** The model, $\mathcal Z_P$, $\mathcal Z_D$, $\mathrm{val}(P)$, $\mathrm{val}(D)$ (extended-real infimum and supremum), $J_\infty$, $J_{\infty\pi}$, maximizers and $p$-optimality are the platform definitions of `MDPFinance.LPDuality`, the same ones on which Theorems 7.5.6 and 7.5.7 are stated. The hypothesis $\mathcal T:I\!M\to I\!M$ says that for $v\in I\!M$ the extended-real function $\mathcal Tv$ is a real function in $I\!M$.
--
--   Differences from the source:
--   - generalization: p is the initial distribution of X_0 (a probability measure) with ∫ b dp < ∞ → p is any measure on E with ∫ b dp < ∞; reason: every quantity is linear in p, so the result holds for every such measure; probability measures are the special case (Example 7.5.10 itself uses p ≡ 1 on two states)
--   - encoding: Q a stochastic kernel from D to E and r a measurable function on D → Q a Markov kernel and r a measurable function on E × A (platform MarkovDecisionModel); reason: only the values on D enter any statement; every kernel and reward on D extends to E × A
--   - encoding: measures μ on D with ∫ b dμ < ∞ → measures μ on E × A with μ(D) = μ(E × A) and ∫ b dμ < ∞ (platform Mb); reason: since b ≥ 1 such μ is finite, so μ(D) = μ(E × A) says μ is carried by D
--   - encoding: val(P) and val(D) as minimal and maximal values → EReal infimum over Z_P and supremum over Z_D (platform valP, valD); reason: the extended reals have no default value for empty or unbounded sets; optimality is stated as attainment
--   - encoding: J_{∞π} = 𝔼^π_x[Σ_k β^k r(X_k, f_k(X_k))] → J_{∞π} := lim sup_n J_{nπ} with J_{nπ} = T_{f_0}…T_{f_{n−1}} 0 (platform Jinfpi); reason: the book shows J_{∞π} = lim_n J_{nπ} under (C) (p.197), and contracting models satisfy (C) (Remark 7.3.2 b))
--   - encoding: IM a closed linear subspace of IB_b, 0 ∈ IM → IsClosedSubspaceOf b IM: IM ⊆ IB_b, 0 ∈ IM, closed under + and scalars, closed under ‖·‖_b-limits in IB_b; reason: IB_b is complete, so limits of sequences in IM lie in IB_b; this is closedness
--   - encoding: T : IM → IM → for v ∈ IM there is w ∈ IM with T v = w (T the extended-real platform operator); reason: under a bounding function T v is real-valued; this says it lies in IM
--   - encoding: val(P) = ∫ J_∞(x) p(dx) → val(P) = erealIntegral p J_∞ together with v* = J_∞ and ∫ v* dp = val(P); reason: the extended-real integral of J_∞ = v* is the Bochner integral of v*, which is integrable
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 7.5.8, p.218 (PDF 229); setting §7.5.2, p.215 (PDF 226); assumptions of Theorem 7.3.5, p.207 (PDF 218)

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- **Theorem 7.5.8 (Strong duality)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 7.5.8, p.218, PDF 229). Suppose the assumptions of
Theorem 7.3.5 are satisfied for the closed subspace `IM ⊂ IB_b`. Then:
a) (P) has an optimal solution `v* ∈ IM`, `v* = J_∞` and `val(P) = ∫ J_∞(x) p(dx) = val(D)`.
b) (D) has an optimal solution `μ* ∈ M_b` and there exists an `f* ∈ F` such that
`val(D) = ∫ r dμ* = ∫ J_{f*}(x) p(dx)`. In particular, the stationary policy `(f*, f*, …)` is
`p`-optimal.

Hypotheses. The standing setting of §7.5.2 (p.215): a contracting model (Definition 7.3.1:
bounding function `b` with constants `c_r, α_b`, and `βα_b < 1`), `b ≥ 1`, `∫ b dp < ∞`, `IM` a
closed linear subspace of `IB_b` with `b ∈ IM`. The assumptions of Theorem 7.3.5 (p.207):
(i) `0 ∈ IM` (part of `IsClosedSubspaceOf`), (ii) `T : IM → IM`, (iii) every `v ∈ IM` has a
maximizer in `Δ ⊂ F`.

**Formalization Note** `T`, `L`, maximizers, `J_∞`, `J_{∞π}`, `Z_P`, `Z_D`, `val(P)`, `val(D)`,
and `p`-optimality are the platform definitions of `MDPFinance.LPDuality`: `val(P)`/`val(D)` are
`EReal` infimum/supremum over the feasible sets, `J_{∞π}` is `lim sup_n J_{nπ}` (the book's
`J_{∞π} = lim_n J_{nπ}`, p.197), `J_{f*}` is `J_{∞π}` for the constant policy, and `p`-optimality
is over Markov policies `F^∞`. Hypothesis (ii) uses the `EReal` operator `T` on `v` viewed as an
`EReal`-valued function and asks for a real `w ∈ IM` with `T v = w`. `p` is any measure with
`∫ b dp < ∞` (the book's initial distribution is the probability case). -/
theorem theorem_7_5_8 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    (hb1 : ∀ x, 1 ≤ b x) (hαb : M.β * αb < 1)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤)
    (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs) (Δ : Set (E → A))
    (hT : ∀ v ∈ IMs, ∃ w ∈ IMs, T M (fun x => (v x : EReal)) = fun x => (w x : EReal))
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f) :
    (∃ vstar ∈ ZP M IMs, (∀ x, Jinf M x = (vstar x : EReal)) ∧
        ((∫ x, vstar x ∂p : ℝ) : EReal) = valP M IMs p ∧
        valP M IMs p = erealIntegral p (Jinf M) ∧ valP M IMs p = valD M b IMs p) ∧
      (∃ μstar ∈ ZD M b IMs p, ((∫ xa, M.r xa ∂μstar : ℝ) : EReal) = valD M b IMs p ∧
        ∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
          valD M b IMs p = erealIntegral p (Jinfpi M M.r fun _ => fstar) ∧
          IsPOptimal M p fun _ => fstar) := by sorry

end BauerleRiederMDP.LPDuality
