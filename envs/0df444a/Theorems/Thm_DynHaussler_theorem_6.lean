-- Prove2me | Theorems.Thm_DynHaussler_theorem_6
-- name    : DynHaussler.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:54.198925+00:00
-- url     : https://prove2.me/theorems/dfe64392-3b03-4fa5-923b-31226a11bf47
-- title:
--   Theorem 6 — matching lower bound $N^{\mathrm{dyn}}_p(H_d,\varepsilon,T)>(1/(2^{p+1}\varepsilon^p))^d$
-- statement:
--   For every integer $d\ge1$ there are a countable domain $X_d$ and a countable binary class $H_d\subseteq\{0,1\}^{X_d}$ with $\mathrm{Ldim}(H_d)=\mathrm{sfat}_\gamma(H_d)=d$ for all $0<\gamma\le1$, such that, for every $1\le p<\infty$ and every $0<\varepsilon<2^{-1-1/p}$, there are an integer $T_0=T_0(d,p,\varepsilon)\ge1$ and an infinite periodic instance sequence $(\bar x_t)_{t\ge1}$ in $X_d$ for which every integer $T\ge T_0$ satisfies
--   $$
--   N^{\mathrm{dyn}}_p(H_d,\varepsilon,T)>\Bigl(\frac{1}{2^{p+1}\varepsilon^p}\Bigr)^d. \tag{21}
--   $$
--   For every such $T$ the lower bound holds even when covering is required only on the prefix $\bar x_{1:T}$ and the covering predictions are arbitrary vectors: any $n$ vectors $w^1,\dots,w^n\in\mathbb R^T$ such that every $h\in H_d$ has some $\rho_{p,T}(w^i,h[\bar x_{1:T}])\le\varepsilon$ number $n>(1/(2^{p+1}\varepsilon^p))^d$. The class and its domain depend only on $d$; $T_0$ and the periodic sequence may depend on $d,p,\varepsilon$, but not on $T$.
--
--   This is the lower half of the goal: the exponent $pd$ in the upper bound cannot be improved, for one fixed class at every accuracy in range and every long horizon.
--
--   **Formalization Note** The domain and class are existential and chosen before $p$ and $\varepsilon$; $T_0$ and $\bar x$ are chosen after $(p,\varepsilon)$ and before $T$. The sequence is 0-based, $\bar x:\mathbb N\to X_d$, and periodic means $\bar x(t+L)=\bar x(t)$ for some $L>0$ and all $t$.
--
--   Differences from the source:
--   - generalization: covering predictions are arbitrary vectors in [0,1]^T → arbitrary vectors in ℝ^T; reason: a cover by vectors in [0,1]^T is a cover by vectors in ℝ^T, so the Lean bound implies the source's
--   - encoding: a binary class H_d ⊆ {0,1}^{X_d} → a set of real functions with values 0 or 1; reason: the same functions, viewed in [0,1]^X
--   - encoding: the infinite sequence (x̄_t)_{t≥1} and its prefix x̄_{1:T} → xbar : ℕ → X (0-based) and the prefix t ↦ xbar t, t < T; reason: index shift only
--   - encoding: N^dyn_p ∈ ℕ ∪ {∞} compared with real numbers → dynCoverNum in ℕ∞, compared through ℕ∞ → ℝ≥0∞ with ENNReal.ofReal of the real bound; reason: same order on the nonnegative extended reals
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Theorem 6, Eq. (21), p.15 (PDF p.17); proof pp.46–49 (PDF pp.48–51)

import Mathlib
import Definitions.Def_DynHaussler_dynCoverNum
import Definitions.Def_DynHaussler_ldim
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler

/-- **Theorem 6 (Matching `ℓ_p` lower bound).** For every integer `d ≥ 1`, there are a countable domain
`X_d` and a countable binary class `H_d ⊆ {0,1}^{X_d}` with `Ldim(H_d) = sfat_γ(H_d) = d` for all
`0 < γ ≤ 1`, such that, for every `1 ≤ p < ∞` and every `0 < ε < 2^{−1−1/p}`, there are an integer
`T_0 = T_0(d, p, ε) ≥ 1` and an infinite periodic instance sequence `(x̄_t)_{t ≥ 1}` in `X_d` for which
every integer `T ≥ T_0` satisfies `N^dyn_p(H_d, ε, T) > (1/(2^{p+1} ε^p))^d` (Eq. (21)). For every such
`T`, the lower bound holds even when covering is required only on the prefix `x̄_{1:T}` and the
covering predictions are arbitrary vectors in `[0,1]^T`. The class and its domain depend only on
`d`; `T_0` and the periodic sequence may depend on `d, p`, and `ε`, but not on `T`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…), Theorem 6, Eq. (21), p.15 (PDF p.17); proof pp.46–49 (PDF pp.48–51).

**Formalization Note** The domain and class are existential and are chosen before `p` and `ε`; `T_0`
and `x̄` are chosen after `(p, ε)` and before `T`. The sequence is 0-based, `x̄ : ℕ → X_d`, with prefix
`(x̄_0, …, x̄_{T−1})`; "periodic" is `∃ L > 0, ∀ t, x̄(t + L) = x̄(t)`. The binary class is a set of real
functions with values in `{0,1}`. The fixed-prefix clause is stated for arbitrary covering vectors in
`ℝ^T` (not only `[0,1]^T`): any `n` vectors that cover every `h ∈ H_d` on the prefix number more than
`(1/(2^{p+1} ε^p))^d`. Real powers are `Real.rpow`; `N^dyn_p` lies in `ℕ∞` and is compared in `ℝ≥0∞`. -/
theorem theorem_6 :
    ∀ d : ℕ, 1 ≤ d →
      ∃ (X : Type) (_ : Countable X) (H : Set (X → ℝ)), H.Countable ∧
        (∀ h ∈ H, ∀ x, h x = 0 ∨ h x = 1) ∧ ldim H = d ∧
        (∀ γ : ℝ, 0 < γ → γ ≤ 1 → NondualOpt.sfat H γ = d) ∧
        ∀ p : ℝ, 1 ≤ p → ∀ ε : ℝ, 0 < ε → ε < (2 : ℝ) ^ (-1 - 1 / p) →
          ∃ T₀ : ℕ, 1 ≤ T₀ ∧ ∃ xbar : ℕ → X, (∃ L : ℕ, 0 < L ∧ ∀ t, xbar (t + L) = xbar t) ∧
            ∀ T : ℕ, T₀ ≤ T →
              ENNReal.ofReal ((1 / ((2 : ℝ) ^ (p + 1) * ε ^ p)) ^ d) <
                ((dynCoverNum p ε H T : ℕ∞) : ENNReal) ∧
              ∀ (n : ℕ) (W : Fin n → Fin T → ℝ),
                (∀ h ∈ H, ∃ i : Fin n, rho p (W i) (fun t => h (xbar t)) ≤ ε) →
                (1 / ((2 : ℝ) ^ (p + 1) * ε ^ p)) ^ d < n := by sorry

end DynHaussler
