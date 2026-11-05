-- Prove2me | Theorems.Thm_BlindNRMLS_theorem_3
-- name    : BlindNRMLS.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:11.27427+00:00
-- url     : https://prove2.me/theorems/bc9a80f7-f537-4b44-9fee-de0590e0f2c1
-- title:
--   Theorem 3 (corrected: $T\ge2$ and $n\le(d+1)\log[(d+1)KT](\log T)^2$) — LS-2SLP is an $s$-switch policy with the rate
-- statement:
--   For all bounds $a_{\max},p_{\max}$ on the entries there are $c,c'>0$ such that the following holds. Let $b>0$, and let a BNRM problem have $T\ge2$, $K>d+1$ and $B_i\ge bT$ for all $i$. Then for every $s$ an LS-2SLP policy exists, and every LS-2SLP policy $\phi$ is in $\Phi[s]$ and satisfies $R^\phi_s(T)\le R^\phi(T)$. If moreover $n\le(d+1)\log[(d+1)KT](\log T)^2$, then, with $\nu=\nu(s,d)$,
--   $$
--   R^\phi(T)\le\max\{c/b,c'\}\,\sqrt{n^3(d+1)\log[(d+1)KT]}\,K^{1-\frac1{2-2^{-\nu}}}\log T\cdot T^{\frac1{2-2^{-\nu}}} .
--   $$
--   This is the upper half of the optimal rate.
--
--   Differences from the source:
--   - correction: T ≥ 1 → T ≥ 2; reason: at T = 1 the bound is 0 but the regret is at least 1/3: T=1, d=0, K=n=2, prices (1,0) and (1/2,0), demand (0,1) on product 1 for arms (1,2) and the swapped Q
--   - correction: the bound for every n → the bound under n ≤ (d+1) log[(d+1)KT] (log T)²; existence and the s-switch claim for every n; reason: epoch 1 may consume n a_max t₁, not the √n(…) of (EC.20); d=1, K=3, s=4, n≈(log T)⁵, B₁=n t₁/12 with costly arms 2, 3 beats any fixed c, c′ (paper notes C2)
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
--   - generalization: clairvoyant policies have the signature R^d × [s] × [T] → Δ([K]) → clairvoyant policies are all history-dependent policies with at most s switches a.s. under that Q; reason: this class contains the page's, and the signature omits the last action, which a switch-limited policy must know
--   - reading: Algorithm 2 overlooks rounding, and leaves infeasible LPs, empty samples, the order within an epoch and z₀ open → ⌈γN_k⌉₊ periods; explore solutions optimal with at most d+2 non-zeros, else 0; q̄ = 0 and old bounds when n_k = 0; any order from the current arm; any fixed z₀; reason: (EC.19) needs n_k ≥ γN_k and a basic solution of an LP with d+2 constraints; a random z₀ is a mixture
--   - generalization: c, c′ are absolute constants completely determined by a_max, p_max → for all bounds amax, pmax on the entries there exist c, c′; Algorithm 2 uses its own a_max computed from A; reason: this is the printed quantifier order made explicit, for every value of the bounds
--   - generalization: d < min{n,K} − 1 is assumed for ease of presentation (p.8) → not imposed beyond the theorem's K > d+1; reason: the printed theorem and its proof do not use n > d+1
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Theorem 3, p.18

import Mathlib
import Definitions.Def_BlindNRMLS_switchRegret
import Definitions.Def_BlindNRMLS_IsLS2SLP

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Theorem 3 (corrected): for all bounds `amax, pmax` on the entries there are `c, c' > 0` such that,
for every problem with `T ≥ 2`, `K > d + 1`, `B_min ≥ bT` and every `s`, LS-2SLP exists, it
is an `s`-switch learning policy, `R^ϕ_s(T) ≤ R^ϕ(T)`, and, when `n ≤ (d+1) log[(d+1)KT] (log T)²`,
`R^ϕ(T) ≤ max{c/b, c'} √(n³(d+1) log[(d+1)KT]) K^{1-1/(2-2^{-ν})} log T · T^{1/(2-2^{-ν})}`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Theorem 3, p.18.

**Formalization Note.** The constants are chosen before all the other parameters except `amax, pmax`
("completely determined by `a_max, p_max`"). `T ≥ 2`: at `T = 1` the bound is `0` and the regret
is not. The cap on `n` sits only on the regret bound. -/
theorem theorem_3 (amax pmax : ℝ) :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧
      ∀ (b : ℝ) (d n K : ℕ) (P : Problem d n K) (s : ℕ),
        0 < b → 2 ≤ P.T → d + 1 < K →
        (∀ i j, P.A i j ≤ amax) → (∀ k j, P.p k j ≤ pmax) →
        (∀ i, b * (P.T : ℝ) ≤ P.B i) →
        (∃ φ, IsLS2SLP P s φ) ∧
        ∀ φ, IsLS2SLP P s φ →
          φ ∈ LearningClass P s ∧ switchRegret P s φ ≤ regret P φ ∧
          ((n : ℝ) ≤ nCap P.T d K →
            regret P φ ≤ max (c / b) c' * upperBracket P.T d K n (nu s d K)) := by sorry

end BlindNRMLS
