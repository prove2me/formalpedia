-- Prove2me | Theorems.Thm_CubicProductLB_eq_346
-- name    : CubicProductLB.eq_346
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:36.295818+00:00
-- url     : https://prove2.me/theorems/a416e52e-fe8f-4eb9-93d7-9246db6ac04f
-- title:
--   Eqs. (344), (346) — the target bit is a constant plus at most $C$ bounded-observation bits
-- statement:
--   There is an absolute integer $R \ge 1$ such that the following holds for every target prime $q > 3$, every $n$ and every cubic representation of $F_{q,n}$ of occurrence cost $C$. Let $P_1, \dots, P_S$ be its positive-cost factors. Then
--   $$S \le C,$$
--   every negative-sign bit $b_{P_j}$ has an $R$-observation representation over $\mathbb F_3$, and there is a constant $\delta \in \mathbb F_2$ with
--   $$b_{q,n}(z) = \delta + \sum_{j=1}^S b_{P_j}(z) \pmod 2 \quad \text{for every } z \in \{0,1\}^n.$$
--   Apart from one global constant, the target is thus a modulo-two sum of at most $C$ functions, each having at most $R$ affine observations.
--
--   Differences from the source:
--   - reading: "an absolute integer R ≥ 1, independent of n, of the factor Pj, and of the representation", with q fixed at the start of the proof → ∃ R before ∀ q; reason: R is the constant of Lemma 12, whose statement does not involve q
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Steps 1–3, Eqs. (344), (346), pp.38–39

import Mathlib
import Definitions.Def_CubicProductLB_ProductRep
import Definitions.Def_CubicProductLB_CubicRep
import Definitions.Def_CubicProductLB_targetBit
import Definitions.Def_CubicProductLB_HasObsRep
import Definitions.Def_CubicProductLB_negBit

namespace CubicProductLB

/-- Eqs. (344), (346) (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Steps 1–3, Eqs. (344), (346), pp.38–39). There is an
absolute `R ≥ 1` such that every cubic representation of `F_{q,n}`, with positive-cost factors
`P_1, …, P_S`, satisfies `S ≤ C`, every bit `b_{P_j}` has an `R`-observation representation over `F_3`, and
`b_{q,n} = δ + ∑_j b_{P_j}` over `F_2` for a constant `δ`.

**Formalization Note** `R` is the constant of Lemma 12, "independent of n, of the factor Pj, and of the
representation" (p.38); as that constant is absolute, it also comes before `q`. -/
theorem eq_346 :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ q : ℕ, q.Prime → 3 < q → ∀ (n : ℕ) (r : CubicRep q n),
      r.posCount ≤ r.cost ∧ (∀ l ∈ r.posFactors, HasObsRep R (negBit l)) ∧
      ∃ δ : ZMod 2, ∀ z : Fin n → Bool,
        targetBit q n z = δ + (r.posFactors.map fun l => negBit l z).sum := by sorry

end CubicProductLB
