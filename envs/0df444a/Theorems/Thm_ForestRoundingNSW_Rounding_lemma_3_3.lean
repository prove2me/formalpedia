-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_lemma_3_3
-- name    : ForestRoundingNSW.Rounding.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:52:10.027755+00:00
-- url     : https://prove2.me/theorems/7f93a664-5a5e-44d7-9e2b-3e873a162fe1
-- title:
--   Lemma 3.3 — on a forest, Algorithm 2 returns disjoint bundles, each with exactly Algorithm 1's law, in polynomially many operations
-- statement:
--   Let $y\in P$ have a support graph that is a forest, and for every agent $i$ let $f_i:2^G\to\mathbb R_{\ge0}$ be normalized, monotone and submodular with multilinear extension $F_{f_i}$. Given exact gradients of the $F_{f_i}$, Algorithm 2 returns pairwise-disjoint bundles $(S_i)_{i\in N}$ such that each $S_i$ has the same distribution as the output of Algorithm 1 applied to $f_i$ and $y_i$:
--   $$S_i\ \stackrel{d}{=}\ \mathrm{Alg1}(f_i,y_i)\quad\text{for every }i,\qquad S_i\cap S_{i'}=\emptyset\ \ (i\ne i').$$
--   The algorithm uses polynomially many arithmetic operations and oracle evaluations.
--
--   The statement has two parts. First, for every rooting of the support forest at items and all choice rules, every outcome of Algorithm 2's joint law has pairwise-disjoint bundles and the law of each $S_i$ is Algorithm 1's law for $(f_i,y_i)$ with the same rule. Second, there are a universal constant $C_0$ and one admissible program on the randomized oracle real RAM such that, for every instance, every run halts within $C_0(n+m)^{C_0}+C_0$ steps and outputs pairwise-disjoint bundles, and the law of the output under the uniform tape equals Algorithm 2's joint law for some choice rules and some rooting.
--
--   The joint law of different agents' bundles is not claimed beyond disjointness.
--
--   Differences from the source:
--   - encoding: items G and y ∈ P on N × G → agents Fin n and items Fin m (the item set is G); the program's input has G = all items and no kept bundles; reason: Lean convention; same instances
--   - reading: Algorithm 2 (roots and Algorithm 1's choices unspecified) → part 1 is stated for every rooting of the support forest at items and every family of choice rules; reason: the paper leaves both choices open, so the lemma is claimed for every choice
--   - reading: uses polynomially many arithmetic operations and oracle evaluations → one universal C0 and one admissible program on the oracle real RAM: every run halts within C0·(n+m)^C0 + C0 steps, outputs pairwise-disjoint bundles, and its output law equals Algorithm 2's law for some choice rules and some rooting; reason: the paper's algorithm model with exact oracles; the bound holds on every run
--   - encoding: exact gradients and the algorithm's arithmetic → unit-cost oracle instructions for f_i, F_{f_i}, ∂_j F_{f_i}, rational literals and a uniform [0,1] tape; reason: the exact-evaluation convention of §2.2
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 22, Lemma 3.3; p. 23, Algorithm 2

import Mathlib
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions
import Definitions.Def_ForestRoundingNSW_Rounding_Allocation
import Definitions.Def_ForestRoundingNSW_Rounding_BalancedRounding
import Definitions.Def_ForestRoundingNSW_Rounding_ForestCoupling
import Definitions.Def_ForestRoundingNSW_Rounding_Machine

open MeasureTheory

namespace ForestRoundingNSW.Rounding

theorem lemma_3_3 :
    (∀ (n m : ℕ) (y : Fin n → Fin m → ℝ) (f : Fin n → Finset (Fin m) → ℝ)
        (ρ : Fin n → (Fin m → ℝ) → Fin m × Fin m) (R : Rooting n m),
        InP y → IsForest y → (∀ i, IsNMS (f i)) → (∀ i, IsChoiceRule (ρ i)) → IsRooting y R →
        (∀ A ∈ (alg2Law f ρ y R).support, ∀ i i' : Fin n, i ≠ i' → Disjoint (A i) (A i')) ∧
        ∀ i : Fin n, (alg2Law f ρ y R).map (fun A => A i) = alg1Law (f i) (ρ i) (y i)) ∧
    ∃ C0 : ℕ, ∃ P : Program, Admissible P ∧
      ∀ (n m : ℕ) (y : Fin n → Fin m → ℝ) (f : Fin n → Finset (Fin m) → ℝ),
        InP y → IsForest y → (∀ i, IsNMS (f i)) →
        (∀ ν : Tape, HaltsWithin P f ν (initState n m y Finset.univ (fun _ => ∅))
            (C0 * (n + m) ^ C0 + C0)) ∧
        (∀ ν : Tape, ∀ i i' : Fin n, i ≠ i' →
            Disjoint (outBundles P f (initState n m y Finset.univ (fun _ => ∅)) ν i)
              (outBundles P f (initState n m y Finset.univ (fun _ => ∅)) ν i')) ∧
        ∃ ρ : Fin n → (Fin m → ℝ) → Fin m × Fin m, (∀ i, IsChoiceRule (ρ i)) ∧
          ∃ R : Rooting n m, IsRooting y R ∧
            ∀ A : Fin n → Finset (Fin m),
              tapeLaw {ν | outBundles P f (initState n m y Finset.univ (fun _ => ∅)) ν = A} =
                alg2Law f ρ y R A := by sorry

end ForestRoundingNSW.Rounding
