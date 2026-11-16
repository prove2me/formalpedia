-- Prove2me | Theorems.Thm_DecDynMatch_Supplement_theorem_3
-- name    : DecDynMatch.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:33:47.202218+00:00
-- url     : https://prove2.me/theorems/61d9a519-edcf-409c-82b3-d54f94487458
-- title:
--   Theorem 3 — every protocol with convergence speed $g$ pays $\Omega(N_g(T))$ (static) and $\Omega(t^*+N_g(T))$ (dynamic)
-- statement:
--   Let $K\ge2$, let $g:\mathbb N_{\ge1}\to\mathbb N_{\ge1}$ be non-decreasing, and let $\Pi$ be any randomized decentralized matching protocol (known preferences) with convergence speed $g$. With $s_0=H$, $s_{j+1}=s_j+g(s_j)$ and $N_g(T)=\#\{j\ge0:s_j<T\}$:
--
--   1. **(static)** there is a two-player static instance $I_0$ (both players enter in round 1 and never leave) and constants $c>0$, $T_0$ such that
--   $$
--   \mathbb E[D_\Pi(T;I_0)]\ge c\,N_g(T)\qquad\text{for all } T\ge T_0;
--   $$
--   2. **(dynamic)** there is a constant $c>0$ such that for every $t^*\ge2$ there is a dynamic instance $I'$ whose last population-event time is exactly $t^*$ with
--   $$
--   \mathbb E[D_\Pi(T;I')]\ge c\,\bigl(t^*+N_g(T)\bigr)\qquad\text{for every } T\ge t^* .
--   $$
--
--   All instances have utilities in $[0,1]$. Together with Theorem 2 and Corollary 1 this shows that $\Pi_g$ has the optimal asymptotic mismatch among protocols of convergence speed $g$ up to a $K^2$ factor, and with $g(t)=t$ that SC-DA's bound $O(t^*+K^2\log T)$ is optimal in $t^*$ and in $\log T$ up to $K^2$.
--
--   **Formalization Note** Protocols are `Protocol K`, the expectation is `expD` (a sum of mismatch probabilities) and convergence speed is `HasConvSpeed` (Definition 1, with $c_\varepsilon$ chosen before the instance).
--
--   Differences from the source:
--   - encoding: randomized decentralized protocol with private state and private randomness → Protocol K: one distribution over arms per (own utilities, local history); reason: a player recalls its whole local history, so behavioural rules give the same outcome laws as private state plus private randomness (Kuhn's theorem); same class of protocols
--   - reading: E[D_Π(T; I₀)] = Ω(N_g(T)) → ∃ c > 0, ∃ T₀, ∀ T ≥ T₀, c·N_g(T) ≤ E[D_Π(T; I₀)], with c depending on K, g, Π; reason: Ω is asymptotic in T; for small T the expectation can be 0 (eq. (39) has a −1)
--   - encoding: Ω(t* + N_g(T)) for every t* ≥ 2 and T ≥ t* → one c > 0 chosen before t*, valid for every t* ≥ 2 and T ≥ t*; reason: the paper states the coefficient is independent of t* and T (p.25, eq. (42))
--   - encoding: every instance (Definition 1), two-player instance I₀, instance I′ → instances with utilities in [0, 1] on a finite player type in Type; I₀ on Fin 2; reason: every finite player set is in bijection with such a type and protocols do not see identities; [0, 1] is the paper's range (§2.1)
--   - encoding: g : ℕ≥1 → ℕ≥1 non-decreasing → g : ℕ → ℕ with g t ≥ 1 and g monotone for t ≥ 1; reason: g(0) is never read
--   - encoding: instances with a non-empty final market ("Wlog", §2.3, p.5) → no such condition, in HasConvSpeed or on I₀, I′; reason: on an instance with an empty final market no round after t* is mismatched, so L_Π(h; I) = 0 and the convergence condition adds nothing; I₀ has two permanent players; an I′ with empty final market has E[D_Π(T; I′)] constant for T ≥ t* while N_g(T) → ∞, so it cannot witness the dynamic bound
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 3, pp.10–11, eq. (9); Definition 1, p.10; App. B.1, pp.23–25

import Mathlib
import Definitions.Def_DecDynMatch_Fg
import Definitions.Def_DecDynMatch_Supplement_HasConvSpeed

namespace DecDynMatch.Supplement

open DecDynMatch

/-- **Theorem 3 (Necessary mismatch cost).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic
Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 3, pp.10–11: "For every
K ≥ 2, every non-decreasing function g : ℕ≥1 → ℕ≥1, and every randomized decentralized matching
protocol Π with convergence speed g, the following lower-bounds hold. There exists a two-player
static matching instance I₀ such that E[D_Π(T; I₀)] = Ω(N_g(T)). For every t* ≥ 2, there exists a
dynamic matching instance I′ with last population-event time t* such that, for every T ≥ t*,
E[D_Π(T; I′)] = Ω(t* + N_g(T))." (eq. (9)).

1. (static) There is a two-player instance `I₀` (utilities in `[0, 1]`, both players enter in
   round 1 and never leave) and `c > 0`, `T₀` with `E[D_Π(T; I₀)] ≥ c·N_g(T)` for all `T ≥ T₀`.
2. (dynamic) There is `c > 0` such that for every `t* ≥ 2` there is an instance `I′` (utilities in
   `[0, 1]`) whose last population-event time is exactly `t*`, with
   `E[D_Π(T; I′)] ≥ c (t* + N_g(T))` for every `T ≥ t*`.

**Formalization Note.**
* `g : ℕ → ℕ` is required to be `≥ 1` and non-decreasing on the positive integers only (no `Ω(t)`,
  no computability).
* `Ω(N_g(T))` in the static part is asymptotic in `T` (`∃ c > 0, ∃ T₀, ∀ T ≥ T₀`); `c` may depend on
  `K`, `g`, `Π`. In the dynamic part one `c` serves every `t* ≥ 2` and every `T ≥ t*` (p.25: "The
  coefficient is independent of t* and T"), and `I′` may depend on `Π` and `t*` but not on `T`.
* Protocols are `Protocol K` (local, behaviourally randomized); `E[D_Π]` is `expD`; convergence
  speed is `HasConvSpeed`. -/
theorem theorem_3 (K : ℕ) (hK : 2 ≤ K) (g : ℕ → ℕ) (hg_pos : ∀ t, 1 ≤ t → 1 ≤ g t)
    (hg_mono : ∀ s t, 1 ≤ s → s ≤ t → g s ≤ g t) (prot : Protocol K)
    (hprot : HasConvSpeed prot g) :
    (∃ I₀ : Instance K (Fin 2), UnitUtilities I₀ ∧ (∀ i, I₀.b i = 1 ∧ I₀.d i = ⊤) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → c * (Ng K g T : ℝ) ≤ expD prot I₀ T) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ ts : ℕ, 2 ≤ ts →
        ∃ (ι : Type) (_ : Fintype ι) (I' : Instance K ι), UnitUtilities I' ∧ tstar I' = ts ∧
          ∀ T, ts ≤ T → c * ((ts : ℝ) + (Ng K g T : ℝ)) ≤ expD prot I' T := by sorry

end DecDynMatch.Supplement
