-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_Supplement_theorem_2
-- name    : FakeUserRanking.FORC.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:37:29.821267+00:00
-- url     : https://prove2.me/theorems/f04ddfc3-11a6-4f6e-95e4-b0fc8d1cf516
-- title:
--   Theorem 2, p. 18 — with F known, FAR's regret is O(n²F + Σ_{j<i} log(nT)/Δ_{j,i})
-- statement:
--   **Theorem 2 (known fakeness budget: regret of FAR).** There is an absolute constant $C$ such that the following holds. Let $n,T\ge1$, let $F$ be the fakeness budget, known to the platform and given to FAR, and let the click probabilities satisfy $\mu_1>\mu_2>\dots>\mu_n$, with gaps $\Delta_{j,i}=\mu_j-\mu_i$. Then for every fake-user policy $P$ with fakeness budget $F$ and every resolution of the choices Algorithm 2 leaves open, the regret of FAR satisfies
--
--   $$\mathrm{Reg}_T(P)\;\le\;C\left(n^2F+\sum_{j=1}^{n}\sum_{i=j+1}^{n}\frac{\log(nT)}{\Delta_{j,i}}\right).\qquad(5)$$
--
--   The fake users thus cost FAR an additive $O(n^2F)$, on top of the $O(\sum_{j<i}\log(nT)/\Delta_{j,i})$ regret of learning the ranking without them. Theorem 3 shows that a bound of the same flavour, with a multiplicative instead of an additive dependence on $F$, is possible when $F$ is unknown.
--
--   **Formalization Note** The $O(\cdot)$ is one constant $C$, placed before $n$, $T$, $F$, the instance, the policy and FAR's choices. The supremum over policies in (2) is expressed by quantifying over every policy within budget $F$. Algorithm 2's tie-break must choose one of the tied candidates with the smallest feedback count, which is the hypothesis on `tb`; the arbitrary ranking `fb` on a cyclic graph is any function of FAR's past. Products are `Fin n`, indexed from $0$; the double sum runs over pairs of products with the better product first. The logarithm is natural.
--
--   Differences from the source:
--   - encoding: products, positions and rounds are numbered from 1 → products and positions are `Fin n` and rounds are trajectory indices, all numbered from 0; reason: a relabelling; every instance of the paper corresponds to exactly one Lean instance
--   - encoding: Reg_T = sup over policies P ∈ 𝒫 of the regret against P (2) → the bound holds for every policy P with WithinBudget F P; reason: a bound for every feasible policy is a bound for the supremum
--   - reading: Reg_T = O(n²F + Σ_{j<i} log(nT)/Δ_{j,i}) for FAR, whose GraphRankSelect choices are unspecified → ∃ C, ∀ n ≥ 1, T ≥ 1, F, instance with μ strictly decreasing, policy within budget F, tie-break tb picking a tied candidate and fallback fb: regret ≤ C (n²F + Σ_{j<i} log(nT)/Δ_{j,i}); reason: the O(·) is read as one absolute constant before every other quantifier; the proof's explicit bound (14), p. 23, gives it for every T ≥ 1, and Algorithm 2 fixes only these properties of its choices
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 18, Theorem 2, (5); proof pp. 19–24, with (14), p. 23; Algorithm 1, p. 17

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR

namespace FakeUserRanking.FORC.Supplement

/-- Theorem 2 (Known Fakeness Budget: Regret of FAR Algorithm), p. 18: there is an absolute
constant `C` such that for every instance, every fakeness budget `F` (known to FAR), every
fake-user policy within budget `F` and every resolution of FAR's unspecified choices,
`Reg_T ≤ C (n²F + ∑_{j<i} log(nT)/Δ_{j,i})`. -/
theorem theorem_2 :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 1 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n),
        (∀ h S, S.Nonempty → tb h S ∈ S) →
      ∀ (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)),
        regret inst P (far n T F tb fb) T ≤
          C * ((n : ℝ) ^ 2 * F +
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by sorry

end FakeUserRanking.FORC.Supplement
