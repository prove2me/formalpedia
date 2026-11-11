-- Prove2me | Theorems.Thm_BauerleRiederMDP_Contracting_theorem_7_3_5
-- name    : BauerleRiederMDP.Contracting.theorem_7_3_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:28:44.224925+00:00
-- url     : https://prove2.me/theorems/29b80cec-a5b8-41b4-aa55-de5b177ea172
-- title:
--   Theorem 7.3.5 (Structure Theorem) — contracting models satisfy value iteration, have a unique fixed point and an optimal stationary policy
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a stationary Markov Decision Model with infinite horizon, and let $b$ be a **bounding function**: $b:E\to\mathbb R_+$ is measurable and there are $c_r,\alpha_b\ge0$ with $|r(x,a)|\le c_rb(x)$ and $\int b(x')Q(dx'\mid x,a)\le\alpha_bb(x)$ on $D$. Assume $\beta\alpha_b<1$. Let $\mathbb B_b$ be the measurable $v:E\to\mathbb R$ with $\|v\|_b=\sup_x|v(x)|/b(x)<\infty$, let
--
--   $$\mathcal Tv(x)=\sup_{a\in D(x)}\Big\{r(x,a)+\beta\int v(x')Q(dx'\mid x,a)\Big\},$$
--
--   and call a decision rule $f\in F$ a **maximizer** of $v$ if $\mathcal T_fv=\mathcal Tv$. Let $J_\infty(x)=\sup_\pi\mathbb E^\pi_x[\sum_k\beta^kr(X_k,f_k(X_k))]$ over Markov policies, and $J=\lim_nJ_n$ the limit of the $n$-stage values.
--
--   Suppose there are a set $\mathbb M\subset\mathbb B_b$, closed for $\|\cdot\|_b$, and a set $\Delta\subset F$ such that
--
--   1. $0\in\mathbb M$;
--   2. $\mathcal T$ maps $\mathbb M$ into $\mathbb M$;
--   3. every $v\in\mathbb M$ has a maximizer $f\in\Delta$.
--
--   Then:
--
--   1. $J_\infty\in\mathbb M$, $J_\infty=\mathcal TJ_\infty$ and $J_\infty=J$ (**value iteration**);
--   2. $J_\infty$ is the unique fixed point of $\mathcal T$ in $\mathbb M$;
--   3. $J_\infty$ is the smallest function $v\in\mathbb M$ with $v\ge\mathcal Tv$;
--   4. for every $g\in\mathbb M$ and $n\in\mathbb N_0$,
--   $$\|J_\infty-\mathcal T^ng\|_b\le\frac{(\beta\alpha_b)^n}{1-\beta\alpha_b}\,\|\mathcal Tg-g\|_b ;$$
--   5. $J_\infty$ has a maximizer $f\in\Delta$, and every maximizer $f^*$ of $J_\infty$ defines an optimal stationary policy $(f^*,f^*,\dots)$, i.e. $J_{\infty f^*}=J_\infty$.
--
--   This is the main theorem for contracting Markov Decision Models: the infinite-horizon problem is solved by the fixed point of the Bellman operator, computable by value iteration with an explicit error bound, and optimal policies are stationary.
--
--   **Formalization Note** $J_\infty$ and $J_n$ are defined from the model (the published `MDPFinance.Contracting` bundles), not as fixed points of $\mathcal T$. They are `EReal`-valued; statement 1 includes that $J_\infty$ is real-valued. $\mathcal T$ is `EReal`-valued, with actions outside $D(x)$ contributing $-\infty$; the iterates in statement 4 use its real-valued version.
--
--   Differences from the source:
--   - encoding: Q a stochastic kernel from D to E and r : D → ℝ → Q a Markov kernel on E × A and r measurable on E × A; reason: only values on D enter any statement, and every kernel and reward on D extend to E × A.
--   - encoding: J_{∞π} = 𝔼^π_x[Σ_k β^k r(X_k, f_k(X_k))] → limsup_n J_{nπ}; reason: J_{∞π} = lim_n J_{nπ} under (C) (p.197, Theorem B.1.1), and (C) holds for contracting models (Remark 7.3.2 b)).
--   - encoding: J_∞ = J with J := lim_n J_n → J_n(x) → J_∞(x) in EReal for every x; reason: J is defined as this limit.
--   - encoding: J_∞ ∈ IM → J_∞ real-valued and x ↦ (J_∞ x).toReal ∈ IM; reason: J_∞ is [−∞,∞]-valued by definition, IM consists of real functions.
--   - encoding: IM closed in (IB_b, ‖·‖_b) → sequentially closed for ‖·‖_b; reason: (IB_b, ‖·‖_b) is a normed space.
--   - encoding: T : IM → IM and the iterates T^n g → for v ∈ IM, T v is the cast of some w ∈ IM; T^n g via the real-valued reading of T; reason: by (ii) T v is real on IM, so the reading is exact.
--   - encoding: ‖v‖_b with the convention 0/0 := 0 → Lean's x/0 = 0; reason: every function in IB_b vanishes where b does, so the two agree on IB_b.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, Theorem 7.3.5 (Structure Theorem), p.207 (PDF p.218); Definition 7.3.1, p.205 (PDF p.216); Definition 7.1.1 and (7.1), p.194 (PDF p.205)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_BauerleRiederMDP_Contracting_IsClosedInIBb
import Definitions.Def_BauerleRiederMDP_Contracting_Treal

open MeasureTheory ProbabilityTheory Filter Topology

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

/-- **Theorem 7.3.5 (Structure Theorem)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 7.3.5, p.207, PDF p.218). Let `b` be a bounding function
and `β α_b < 1`. If there exists a closed subset `IM ⊂ IB_b` and a set `Δ ⊂ F` such that
(i) `0 ∈ IM`, (ii) `T : IM → IM`, (iii) for all `v ∈ IM` there exists a maximizer `f ∈ Δ` of
`v`, then:
a) `J_∞ ∈ IM`, `J_∞ = T J_∞` and `J_∞ = J` (Value Iteration);
b) `J_∞` is the unique fixed point of `T` in `IM`;
c) `J_∞` is the smallest `r`-superharmonic function `v ∈ IM`, i.e. the smallest `v ∈ IM` with
   `v ≥ T v`;
d) for `g ∈ IM`, `‖J_∞ − T^n g‖_b ≤ (β α_b)^n / (1 − β α_b) · ‖T g − g‖_b`;
e) there exists a maximizer `f ∈ Δ` of `J_∞`, and every maximizer `f*` of `J_∞` defines an
   optimal stationary policy `(f*, f*, …)`.

**Formalization Note.** The model `M`, the bounding function (`IsBoundingFunction`, Definition
7.3.1), `IB_b`, `‖·‖_b` (`normb`), the `EReal`-valued operators `L`, `T`, maximizers
(`IsMaximizerOf`: a decision rule `f` with `L v (x, f x) = T v x` for all `x`), `J_{∞π}`
(`Jinfpi`), `J_∞` (`Jinf`, the supremum over Markov policies `F^∞`) and `J_n` (`Jn`) are the
published `MDPFinance.Contracting` bundles. `J_∞` and `J_n` are `EReal`-valued and defined from
the model, independently of `T`. Statement a) asserts that `J_∞` is real-valued and that its
real version `x ↦ (J_∞ x).toReal` lies in `IM`; "`J_∞ = J`" with `J := lim_n J_n` (p.197) is
stated as the convergence `J_n(x) → J_∞(x)` in `EReal` for every `x`. (ii) is stated as: for
`v ∈ IM`, `T v` is the cast of some `w ∈ IM`. The iterates `T^n g` in d) use `Treal`, the
real-valued reading of `T` (exact on `IM` by (ii)). `IM` is closed for `‖·‖_b`
(`IsClosedInIBb`), not pointwise. Optimality of `(f*, f*, …)` is
`J_{∞ f*^∞}(x) = J_∞(x)` for all `x`. -/
theorem theorem_7_3_5 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hβαb : M.β * αb < 1)
    (IM : Set (E → ℝ)) (hIMsub : IM ⊆ IBb b) (hIMclosed : IsClosedInIBb b IM)
    (Δ : Set (E → A)) (hΔ : ∀ f ∈ Δ, IsDecisionRuleOf M f)
    (h0 : (0 : E → ℝ) ∈ IM)
    (hT : ∀ v ∈ IM, ∃ w ∈ IM, T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    (hmax : ∀ v ∈ IM, ∃ f ∈ Δ, IsMaximizerOf M (fun y => (v y : EReal)) f) :
    -- a) Value iteration
    ((∀ x, Jinf M x = (((Jinf M x).toReal : ℝ) : EReal)) ∧
        (fun x => (Jinf M x).toReal) ∈ IM ∧
        T M (Jinf M) = Jinf M ∧
        ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (Jinf M x))) ∧
      -- b) unique fixed point of T in IM
      (∀ v ∈ IM, T M (fun y => (v y : EReal)) = (fun y => (v y : EReal)) →
        ∀ x, (v x : EReal) = Jinf M x) ∧
      -- c) smallest r-superharmonic function in IM
      (∀ v ∈ IM, (∀ x, T M (fun y => (v y : EReal)) x ≤ (v x : EReal)) →
        ∀ x, Jinf M x ≤ (v x : EReal)) ∧
      -- d) a-posteriori error bound
      (∀ g ∈ IM, ∀ n : ℕ,
        normb b (fun x => (Jinf M x).toReal - (Treal M)^[n] g x) ≤
          (M.β * αb) ^ n / (1 - M.β * αb) * normb b (fun x => Treal M g x - g x)) ∧
      -- e) maximizers of J_∞ and optimal stationary policies
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end BauerleRiederMDP.Contracting
