-- Prove2me | Theorems.Thm_ElimAgree_theorem_3_8_common_output_disj
-- name    : ElimAgree.theorem_3_8_common_output_disj
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:36:34.677197+00:00
-- url     : https://prove2.me/theorems/9f542275-1e47-4826-a39b-e1315605bab7
-- title:
--   Theorem 3.8 — common-output elimination of $k$ disjointness instances costs $\Theta(1+gn)$
-- statement:
--   Let $\ell=\lfloor(n+1)/4\rfloor$ and write the error as $(1-g)2^{-k}$.
--
--   1. **(a)** For $n\ge3$, $k\ge1$ and $0<g\le1$, every public-coin common-output protocol for $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ with failure probability at most $(1-g)2^{-k}$ on every input — even one whose parties may disagree on failed runs — has cost
--   $$c\ge\frac{g\ell}{8\ln2}-\frac{2}{e\ln2}.$$
--   2. **(b)** Without the subtracted term when the output is determined by the transcript: $c\ge g\ell/(8\ln 2)$.
--   3. **(c)** For $n,k\ge1$ and $0<g\le1$ there is a protocol of cost $\lceil2gn/(1+g)\rceil+1$ with that error.
--   4. **(d)** For $n,k\ge1$, every protocol with error below $2^{-k}$ communicates at least one bit.
--   5. **(e)** There are absolute constants $C_1,C_2>0$ such that for all $n,k\ge1$ and $0<g\le1$,
--   $$C_1(1+gn)\le R^{\mathrm{pub,com}}_{(1-g)2^{-k}}\big(\mathrm{Elim}(\mathrm{DISJ}_n^k)\big)\le C_2(1+gn).$$
--
--   Eliminating any number of disjointness instances below the guessing error costs as much as predicting one instance with advantage $g$ (Braverman–Moitra for $k=1$).
--
--   Differences from the source:
--   - generalization: (c) and (d) under n ≥ 3 → n ≥ 1; reason: the proofs use only n ≥ 1 and the Θ claim needs them for n ≤ 2 (p.11); they specialize to n ≥ 3
--   - reading: (e) "for all n, k and g" → n ≥ 1, k ≥ 1, 0 < g ≤ 1; reason: Theorem A's range (p.1); for n = 0 every answer is 1 and R = 0
--   - encoding: public-coin protocols that may also use private coins; cost in bits → PMF over deterministic protocol trees (private coins absorbed); cost = maximal depth over the support; reason: fixing all coins leaves a deterministic tree, and every distribution over trees is a public-coin protocol
--   - encoding: Θ(1 + gn) with absolute constants → ∃ C₁ C₂ > 0 chosen before n, k, g; reason: this is the meaning of absolute constants
--   - encoding: {0, 1} and subsets of [n] → Bool with DISJ = 1 as true; Finset (Fin n); reason: Lean convention; same instances
--   - encoding: R^{pub,com}_{(1−g)2^{−k}} ≥ bound in (a), (b) → every protocol of cost ≤ c with that error has c ≥ bound; reason: R is the least such c, and the set of such c is nonempty
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 3.8, p.10 (PDF p.12) (= Theorem A, p.1, PDF p.3)

import Mathlib
import Definitions.Def_ElimAgree_disjAns
import Definitions.Def_ElimAgree_nuDisj

namespace ElimAgree

/-- Theorem 3.8 (Common-output disjointness), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.10 (= Theorem A, p.1). With
`ℓ = ⌊(n + 1)/4⌋` and error `(1 − g)2^{−k}`:
* (a) for `n ≥ 3`, `k ≥ 1`, `0 < g ≤ 1`, every public-coin common-output protocol for
  `Elim(DISJ_n^k)` with that pointwise error, even if the parties may disagree, has cost
  `c ≥ gℓ/(8 ln 2) − 2/(e ln 2)`;
* (b) without the subtracted term when the output is determined by the transcript;
* (c) for `n, k ≥ 1` there is a protocol of cost `⌈2gn/(1 + g)⌉ + 1` with that error;
* (d) for `n, k ≥ 1`, every protocol with error below `2^{−k}` communicates at least one bit;
* (e) `R^{pub,com}_{(1−g)2^{−k}}(Elim(DISJ_n^k)) = Θ(1 + gn)` for all `n, k ≥ 1` and
  `0 < g ≤ 1`, with absolute constants.

**Formalization Note.** A public-coin protocol (private coins allowed) is a `PMF` over
deterministic trees; cost is the maximal depth over the support. (a) and (b) are stated for every
protocol of cost `c`, which is the bound on `R^{pub,com}`. (c) and (d) are stated for `n ≥ 1`,
which the `Θ` claim needs. The constants of (e) are chosen before `n, k, g`. -/
theorem theorem_3_8_common_output_disj :
    -- (a) common output, disagreement allowed
    (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → ∀ g : ℝ, 0 < g → g ≤ 1 →
      ∀ (c : ℕ) (μ : PMF (ComProt n k)), CostLE μ c →
        (∀ X Y : Inp n k, comErr disjAns μ X Y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
        g * (ell n : ℝ) / (8 * Real.log 2) - 2 / (Real.exp 1 * Real.log 2) ≤ c) ∧
    -- (b) output determined by the transcript
    (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → ∀ g : ℝ, 0 < g → g ≤ 1 →
      ∀ (c : ℕ) (μ : PMF (OneOfManyCC.Protocol (Inp n k) (Inp n k) (Fin k → Bool))), CostLE μ c →
        (∀ X Y : Inp n k, tdErr disjAns μ X Y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) →
        g * (ell n : ℝ) / (8 * Real.log 2) ≤ c) ∧
    -- (c) upper bound
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ g : ℝ, 0 < g → g ≤ 1 →
      ∃ μ : PMF (ComProt n k), CostLE μ (⌈2 * g * n / (1 + g)⌉₊ + 1) ∧
        ∀ X Y : Inp n k, comErr disjAns μ X Y ≤ ENNReal.ofReal ((1 - g) / 2 ^ k)) ∧
    -- (d) error below 2^{-k} needs at least one bit
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ ε : ℝ, ε < (1 / 2) ^ k →
      ∀ μ : PMF (ComProt n k),
        (∀ X Y : Inp n k, comErr disjAns μ X Y ≤ ENNReal.ofReal ε) → ¬ CostLE μ 0) ∧
    -- (e) Θ(1 + gn) with absolute constants
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ g : ℝ, 0 < g → g ≤ 1 →
      C₁ * (1 + g * n) ≤ (Rcom n k ((1 - g) / 2 ^ k) : ℝ) ∧
        (Rcom n k ((1 - g) / 2 ^ k) : ℝ) ≤ C₂ * (1 + g * n)) := by sorry

end ElimAgree
