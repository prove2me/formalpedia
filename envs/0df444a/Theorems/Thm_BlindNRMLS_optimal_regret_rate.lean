-- Prove2me | Theorems.Thm_BlindNRMLS_optimal_regret_rate
-- name    : BlindNRMLS.optimal_regret_rate
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:19.728222+00:00
-- url     : https://prove2.me/theorems/62884cb0-dcc2-41a2-a1fe-9fccf10ce0e1
-- title:
--   §4.3 (corrected: $T\ge2$ and $n\le(d+1)\log[(d+1)KT](\log T)^2$; see Theorem 3) — the optimal regret is $\tilde\Theta(T^{1/(2-2^{-\nu(s,d)})})$
-- statement:
--   The optimal regret of BNRM-LS is on the order of $\tilde\Theta\big(T^{1/(2-2^{-\lfloor(s-d-1)/(K-1)\rfloor})}\big)$. Explicitly, there are numerical constants $c_L,c_L'>0$ and, for all bounds $a_{\max},p_{\max}$ on the entries, constants $c_U,c_U'>0$ such that, for all $b>0$, $T\ge2$, $d\ge0$, $K\ge2(d+1)$, $n\ge d+1$ and $\mathbf B$ with $B_i/T\in[b,1]$, with $\nu=\nu(s,d)$:
--
--   1. (lower bound, Theorem 4) there is a BNRM problem with this $T$ and $\mathbf B$, pairwise distinct price vectors, entries of $P$ at most $1$ and entries of $A$ at most $2$, such that for every $s$
--   $$
--   \min\{c_Lb,c_L'\}\,(d+1)^{-3}K^{-\frac32-\frac1{2-2^{-\nu}}}(\log T)^{-\frac52}\,T^{\frac1{2-2^{-\nu}}}\le\inf_{\phi\in\Phi[s]}R^\phi_s(T);
--   $$
--   2. (upper bound, Theorem 3) every BNRM problem with this $T$ and $\mathbf B$, entries of $P$ at most $p_{\max}$ and entries of $A$ at most $a_{\max}$ has, for every $s$: $\inf_{\phi\in\Phi[s]}R^\phi_s(T)\le\inf_{\phi\in\Phi[s]}R^\phi(T)$; an LS-2SLP policy exists; and every LS-2SLP policy $\phi$ lies in $\Phi[s]$ and, if $n\le(d+1)\log[(d+1)KT](\log T)^2$,
--   $$
--   R^\phi(T)\le\max\{c_U/b,c_U'\}\,\sqrt{n^3(d+1)\log[(d+1)KT]}\,K^{1-\frac1{2-2^{-\nu}}}\log T\cdot T^{\frac1{2-2^{-\nu}}}.
--   $$
--
--   For fixed $K,d,n,b$ the cap on $n$ holds for all large $T$, so the two sides match up to logarithmic factors. An increase in $d$ raises the order of the optimal regret at a fixed budget.
--
--   Differences from the source:
--   - correction: T ≥ 1 → T ≥ 2; reason: at T = 1 the bound is 0 but the regret is at least 1/3: T=1, d=0, K=n=2, prices (1,0) and (1/2,0), demand (0,1) on product 1 for arms (1,2) and the swapped Q
--   - correction: the bound for every n → the bound under n ≤ (d+1) log[(d+1)KT] (log T)²; existence and the s-switch claim for every n; reason: epoch 1 may consume n a_max t₁, not the √n(…) of (EC.20); d=1, K=3, s=4, n≈(log T)⁵, B₁=n t₁/12 with costly arms 2, 3 beats any fixed c, c′ (paper notes C2)
--   - encoding: T ≥ 1 → T ≥ 2; reason: (log T)^{-5/2} is undefined at T = 1, and 0^(-5/2) = 0 in Lean would make the bound trivial
--   - reading: P is "a finite set of K price vectors", though the proof's price vectors coincide → the conclusion asserts P injective; reason: the stronger reading; the perturbation p_{1,k} = 1 − kε keeps the bound
--   - generalization: "there exist P, A" → the conclusion adds entries of P at most 1 and of A at most 2; reason: the proof's construction has these bounds, which the combination with Theorem 3 needs
--   - generalization: Θ̃(T^{1/(2−2^{−ν})}) → explicit bounds with all factors in K, d, n, b, log T, and the existence and membership clauses; reason: they imply the printed rate for fixed K, d, n, b
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
--   - generalization: clairvoyant policies have the signature R^d × [s] × [T] → Δ([K]) → clairvoyant policies are all history-dependent policies with at most s switches a.s. under that Q; reason: this class contains the page's, and the signature omits the last action, which a switch-limited policy must know
--   - reading: Algorithm 2 overlooks rounding, and leaves infeasible LPs, empty samples, the order within an epoch and z₀ open → ⌈γN_k⌉₊ periods; explore solutions optimal with at most d+2 non-zeros, else 0; q̄ = 0 and old bounds when n_k = 0; any order from the current arm; any fixed z₀; reason: (EC.19) needs n_k ≥ γN_k and a basic solution of an LP with d+2 constraints; a random z₀ is a mixture
--   - generalization: d < min{n,K} − 1 is assumed for ease of presentation (p.8) → not imposed beyond the theorem's K > d+1; reason: the printed theorem and its proof do not use n > d+1
--   - generalization: c, c′ in Theorem 3 are absolute constants completely determined by a_max, p_max → for all bounds amax, pmax on the entries there exist c_U, c_U′, chosen after the numerical c_L, c_L′; reason: the printed quantifier order made explicit, for every value of the bounds; Algorithm 2 uses its own a_max computed from A
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, §4.3, p.21; §1.1, p.3

import Mathlib
import Definitions.Def_BlindNRMLS_switchRegret
import Definitions.Def_BlindNRMLS_IsLS2SLP

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- The optimal regret of BNRM-LS is `Θ̃(T^{1/(2-2^{-⌊(s-d-1)/(K-1)⌋})})`, with explicit bounds: there are
numerical constants `c_L, c_L' > 0` and, for all bounds `amax, pmax` on the entries, constants
`c_U, c_U' > 0` such that, for all `b > 0`, `T ≥ 2`, `K ≥ 2(d+1)`, `n ≥ d + 1` and `B` with
`B_i/T ∈ [b, 1]`:
(i) some problem with this `T`, `B`, distinct price vectors and entries bounded by `1` and `2` has,
for every `s`, minimax `s`-switch regret at least `min{c_L b, c_L'}` times the bracket of Theorem 4;
(ii) every problem with this `T`, `B` and entries bounded by `pmax` and `amax` has, for every `s`:
its minimax `s`-switch regret is at most its minimax overall regret over `Φ[s]`; LS-2SLP exists;
every LS-2SLP policy is in `Φ[s]`, and when `n ≤ (d+1) log[(d+1)KT] (log T)²` its regret is at most
`max{c_U/b, c_U'}` times the bracket of Theorem 3.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, §4.3, p.21 and §1.1, p.3.

**Formalization Note.** "Combining Theorem 3 and Theorem 4": the lower bound holds on one problem
built from the parameters, the upper bound on every problem of the class, so the minimax regret over
the class is pinned. The lower constants are numerical and come first; the upper ones are chosen
after `amax, pmax` ("completely determined by `a_max, p_max`"). The hard problem precedes `s`. `Θ̃` is
replaced by the explicit bounds it abbreviates. The cap on `n` sits only on the upper bound; it holds
for all large `T` at fixed `n`. -/
theorem optimal_regret_rate :
    ∃ cL cL' : ℝ, 0 < cL ∧ 0 < cL' ∧
      ∀ amax pmax : ℝ, ∃ cU cU' : ℝ, 0 < cU ∧ 0 < cU' ∧
      ∀ (b : ℝ) (T d K n : ℕ) (B : Fin d → ℝ),
        0 < b → 2 ≤ T → 2 * (d + 1) ≤ K → d + 1 ≤ n →
        (∀ i, b * (T : ℝ) ≤ B i ∧ B i ≤ (T : ℝ)) →
        (∃ P : Problem d n K, P.T = T ∧ P.B = B ∧ Function.Injective P.p ∧
          (∀ k j, P.p k j ≤ 1) ∧ (∀ i j, P.A i j ≤ 2) ∧
          ∀ s : ℕ, min (cL * b) cL' * lowerBracket T d K (nu s d K) ≤ minimaxSwitchRegret P s) ∧
        ∀ P : Problem d n K, P.T = T → P.B = B →
          (∀ k j, P.p k j ≤ pmax) → (∀ i j, P.A i j ≤ amax) →
          ∀ s : ℕ,
            minimaxSwitchRegret P s ≤ minimaxRegret P s ∧
            (∃ φ, IsLS2SLP P s φ) ∧
            ∀ φ, IsLS2SLP P s φ → φ ∈ LearningClass P s ∧
              ((n : ℝ) ≤ nCap T d K →
                regret P φ ≤ max (cU / b) cU' * upperBracket T d K n (nu s d K)) := by sorry

end BlindNRMLS
