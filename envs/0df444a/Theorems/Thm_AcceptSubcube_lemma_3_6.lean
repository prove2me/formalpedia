-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_3_6
-- name    : AcceptSubcube.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:50.113023+00:00
-- url     : https://prove2.me/theorems/aa45fe64-0f47-44ef-a7ec-f26aec59a5ef
-- title:
--   Lemma 3.6 — positive-budget walk
-- statement:
--   Let $\mathcal I$ be an unweighted Boolean CSP of arity at most $k$ with no empty scopes, $\tau$ an assignment, $r\ge0$ and $g\ge1$ integers, $0<\delta\le1$ and $\xi>0$. There are a polynomial $q$ (independent of $k$) and, for every $k\ge2$, a randomized procedure such that:
--
--   1. on every such input $x=(\mathcal I,\tau,r,g,\delta,\xi)$ it halts within
--   $$T(x)=\Big\lceil\Big(\frac{k(1+\delta)}{\delta}\Big)^r\Big\rceil\cdot q\big(|x|+r+\lceil\log_2(1/\xi)\rceil\big)$$
--   steps, reading a coin string of length $T(x)$;
--   2. if some $\sigma$ has $\mathrm{dist}(\tau,\sigma)\le r$ and $C_{\mathcal I}(\sigma)\le g$, then with probability at least $1-\xi$ it outputs an assignment of cost at most $(1+\delta)g$.
--
--   Without the supposition the time bound still holds and the procedure may fail. The walk gives the $(1+\delta)$-approximation when the target radius is logarithmic.
--
--   Differences from the source:
--   - reading: time (k(1+δ)/δ)^r poly(n, |I|, r, log(1/ξ)) → ⌈(k(1+δ)/δ)^r⌉ · q(|x| + r + ⌈log₂(1/ξ)⌉) steps of one TM2 machine per k, q chosen before k, |x| the bit length of the whole input; reason: |x| bounds n and |I| and also counts the bits of δ and ξ, which a machine must read; k appears explicitly in the base
--   - reading: a randomized procedure … with probability at least 1 − ξ → coin string of length T(x); probability = exact fraction of coin strings; reason: fixed-length fair coins are the paper's model (p.28)
--   - reading: arity at most k (k from §2: "Fix an arity k ≥ 2") → 2 ≤ k; reason: standing assumption of §2, p.9
--   - encoding: δ, ξ real parameters → δ, ξ rational inputs with 0 < δ ≤ 1 and ξ > 0; reason: machine inputs are finite; log(1/ξ) needs ξ > 0
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.6, pp.14–15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube

/-- **Lemma 3.6 (Positive-budget walk).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.6, pp.14–15: "Let I be an unweighted
Boolean CSP of arity at most k with no empty scopes. Given τ, an integer r ≥ 0, an integer budget
g ≥ 1, and 0 < δ ≤ 1, suppose some σ has dist(τ, σ) ≤ r and C_I(σ) ≤ g. A randomized procedure
finds an assignment of cost at most (1 + δ)g with probability at least 1 − ξ in time
(k(1 + δ)/δ)^r poly(n, |I|, r, log(1/ξ)). (6) Without the supposition the same time bound holds and
the procedure may fail."

There is a polynomial `q` (independent of `k`) and, for every `k`, a machine reading
`x = (I, τ, r, g, δ, ξ)` and a coin string of length `T(x) = ⌈(k(1+δ)/δ)^r⌉ · q(|x| + r +
⌈log₂(1/ξ)⌉)` that halts within `T(x)` steps on every admissible input, and that, whenever some `σ`
has `dist(τ, σ) ≤ r` and `C_I(σ) ≤ g`, outputs an assignment of cost `≤ (1 + δ)g` for at least a
`1 − ξ` fraction of the coin strings.

**Formalization Note.** Inputs: `I` any well-formed instance of arity `≤ k` with no empty scope
(repeated scopes allowed), `τ` a list of `n` bits, `r ≥ 0`, `g ≥ 1`, `δ ∈ (0,1]` and `ξ > 0`
rational. `poly(n, |I|, r, log(1/ξ))` is read as `q` of the bit length `|x|` of the whole input
(which bounds `n` and `|I|`) plus `r` plus `⌈log₂(1/ξ)⌉`. `k ≥ 2` is the paper's standing arity
(p.9). The coin string has the length of the time bound (a machine reads at most that many coins). -/
theorem lemma_3_6 :
    ∃ q : Polynomial ℕ, ∀ k : ℕ, 2 ≤ k →
      ∃ walk : (GInst × List Bool × ℕ × ℕ × ℚ × ℚ) × List Bool → List Bool,
        let T : GInst × List Bool × ℕ × ℕ × ℚ × ℚ → ℕ := fun x =>
          ⌈((k : ℝ) * (1 + (x.2.2.2.2.1 : ℝ)) / (x.2.2.2.2.1 : ℝ)) ^ x.2.2.1⌉₊ *
            q.eval ((encWalk x).length + x.2.2.1 + ⌈Real.logb 2 (1 / (x.2.2.2.2.2 : ℝ))⌉₊)
        let Adm : GInst × List Bool × ℕ × ℕ × ℚ × ℚ → Prop := fun x =>
          x.1.WellFormed ∧ x.1.MaxArity k ∧ x.1.NoEmptyScope ∧ x.2.1.length = x.1.n ∧
            1 ≤ x.2.2.2.1 ∧ 0 < x.2.2.2.2.1 ∧ x.2.2.2.2.1 ≤ 1 ∧ 0 < x.2.2.2.2.2
        ComputesWithinOn (fun y => Adm y.1 ∧ y.2.length = T y.1) encWalkCoins encAssign walk
            (fun y => T y.1) ∧
        ∀ x, Adm x →
          (∃ σ : Fin x.1.n → Bool, hdist (asg x.1 x.2.1) σ ≤ x.2.2.1 ∧ cost x.1 σ ≤ x.2.2.2.1) →
          1 - (x.2.2.2.2.2 : ℝ) ≤
            coinFrac (T x) (fun w => (cost x.1 (asg x.1 (walk (x, w))) : ℝ) ≤
              (1 + (x.2.2.2.2.1 : ℝ)) * (x.2.2.2.1 : ℝ)) := by sorry

end AcceptSubcube
