-- Prove2me | Theorems.Thm_BlindNRMLS_theorem_4
-- name    : BlindNRMLS.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:00.180511+00:00
-- url     : https://prove2.me/theorems/d891e134-946a-4ceb-a856-f0e2104ff91b
-- title:
--   Theorem 4 — the lower bound, for distinct price vectors
-- statement:
--   There are numerical constants $c,c'>0$ such that the following holds. For all $b>0$, $T\ge2$, $d\ge0$, $K\ge2(d+1)$, $n\ge d+1$ and $\mathbf B$ with $B_i/T\in[b,1]$ for all $i$, there is a BNRM problem with this $T$ and $\mathbf B$, with pairwise distinct price vectors, with entries of $P$ at most $1$ and entries of $A$ at most $2$, such that for every $s\ge0$ and every $\phi\in\Phi[s]$, with $\nu=\nu(s,d)$,
--   $$
--   R^\phi(T)\ge R^\phi_s(T)\ge\min\{cb,c'\}\,(d+1)^{-3}K^{-\frac32-\frac1{2-2^{-\nu}}}(\log T)^{-\frac52}\,T^{\frac1{2-2^{-\nu}}} .
--   $$
--   This is the lower half of the optimal rate: the budget $s$ enters only through $\nu(s,d)$, so each resource costs one extra switch.
--
--   Differences from the source:
--   - encoding: T ≥ 1 → T ≥ 2; reason: (log T)^{-5/2} is undefined at T = 1, and 0^(-5/2) = 0 in Lean would make the bound trivial
--   - reading: P is "a finite set of K price vectors", though the proof's price vectors coincide → the conclusion asserts P injective; reason: the stronger reading; the perturbation p_{1,k} = 1 − kε keeps the bound
--   - generalization: "there exist P, A" → the conclusion adds entries of P at most 1 and of A at most 2; reason: the proof's construction has these bounds, which the combination with Theorem 3 needs
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
--   - generalization: clairvoyant policies have the signature R^d × [s] × [T] → Δ([K]) → clairvoyant policies are all history-dependent policies with at most s switches a.s. under that Q; reason: this class contains the page's, and the signature omits the last action, which a switch-limited policy must know
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Theorem 4, p.19

import Mathlib
import Definitions.Def_BlindNRMLS_switchRegret
import Definitions.Def_BlindNRMLS_nu

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Theorem 4: there are numerical `c, c' > 0` such that for all `b > 0`, `T ≥ 2`, `K ≥ 2(d+1)`,
`n ≥ d + 1` and `B` with `B_i/T ∈ [b, 1]`, some problem with this `T` and `B`, distinct price vectors,
entries of `P` at most `1` and entries of `A` at most `2` has, for every `s` and every `ϕ ∈ Φ[s]`,
`R^ϕ(T) ≥ R^ϕ_s(T) ≥ min{cb, c'} (d+1)^{-3} K^{-3/2-1/(2-2^{-ν})} (log T)^{-5/2} · T^{1/(2-2^{-ν})}`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Theorem 4, p.19.

**Formalization Note.** The constants precede every parameter, and the problem precedes `s` and `ϕ`.
`T ≥ 2`, since `(log T)^{-5/2}` is undefined at `T = 1`. Distinct price vectors are the stronger reading
of "a finite set of `K` price vectors"; the proof's own `P` has coinciding price vectors. -/
theorem theorem_4 :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧
      ∀ (b : ℝ) (T d K n : ℕ) (B : Fin d → ℝ),
        0 < b → 2 ≤ T → 2 * (d + 1) ≤ K → d + 1 ≤ n →
        (∀ i, b * (T : ℝ) ≤ B i ∧ B i ≤ (T : ℝ)) →
        ∃ P : Problem d n K, P.T = T ∧ P.B = B ∧ Function.Injective P.p ∧
          (∀ k j, P.p k j ≤ 1) ∧ (∀ i j, P.A i j ≤ 2) ∧
          ∀ (s : ℕ) (φ : Policy n K), φ ∈ LearningClass P s →
            switchRegret P s φ ≤ regret P φ ∧
            min (c * b) c' * lowerBracket T d K (nu s d K) ≤ switchRegret P s φ := by sorry

end BlindNRMLS
