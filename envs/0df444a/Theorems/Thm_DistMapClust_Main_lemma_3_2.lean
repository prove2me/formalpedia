-- Prove2me | Theorems.Thm_DistMapClust_Main_lemma_3_2
-- name    : DistMapClust.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:06:29.86348+00:00
-- url     : https://prove2.me/theorems/7ec3afc2-497f-445c-bca3-f09cd7a02517
-- title:
--   Lemma 3.2 — polynomially many polylog-size candidate distance sets, one of them ε-relevant, in polynomial time
-- statement:
--   Let $\varepsilon\in(0,1/48)$ and let $I=(P,F,\delta,f,H)$ be an instance of k-Clustering with Linear Distance Mappings (with $k\ge2$ and $n\ge2$, the standing assumption of §3). Given $I$ and $\varepsilon$ one can compute, in time $\mathrm{poly}(|I|,k,d,1/\varepsilon)$, a collection $\mathcal D$ of sets containing $\infty$, each of size $\mathrm{poly}(\log n,k,d,\psi,1/\varepsilon)$, one of which is a set of $\varepsilon$-relevant distances. Formally: for every class constant $c$ there are a program and universal $C,e$ such that on every such instance, size parameter $s\ge n,k,d,\psi$ with $2^{-s^c}\le\mathrm{OPT}_I\le2^{s^c}$, and every tape,
--   $$\text{steps}\le C\,(s\,k\,d\,\lceil1/\varepsilon\rceil)^e+C,\qquad |D|\le C\,(\log_2n\cdot k\,d\,\psi/\varepsilon)^e+C\ \ (D\in\mathcal D),$$
--   and for every optimal solution $(X^*,\sigma^*)$ some $D\in\mathcal D$ is $\varepsilon$-relevant for it. It restricts the distances the center-finding algorithm has to guess to a polylogarithmic set.
--
--   **Formalization Note.** The output sets are read through `outSet`, which adds `∞`; the program must write nonnegative finite elements. The program receives `ε` and the coefficients in real memory and evaluates `f` through its oracle.
--
--   Differences from the source:
--   - reading: an algorithm running in time … (bit model, §A.1; the Ball Intersection Algorithm 'supplied only as an oracle', §2.1) → one program of the unit-cost randomized oracle real RAM `DistMapClust_Main_Machine` (published SmaleNinth real-RAM core, uniform tape, no floor or other real-to-integer conversion, opaque point registers; one step per instruction including the oracles dist, ballInt, evalObj, evalNorm, evalMap, lam); reason: the paper fixes no machine; points of a possibly infinite F are reachable only through distances and the oracle (p. 8: the algorithm 'accesses only the distances')
--   - reading: poly(|I|), |I| the bit size, and §A.1 assumption 3: 2^{−poly(|I|)} ≤ OPT_I ≤ 2^{poly(|I|)} → a size parameter s given as input with n, k, d, ψ ≤ s; poly(|I|) = C·s^e + C with universal C, e fixed before the instance; hypothesis OptBounded s c OPT_I (2^{−s^c} ≤ OPT_I ≤ 2^{s^c}) for a class constant c quantified before the program; reason: the bit size of an instance with opaque points and infinite F has no meaning on a real RAM; §A.1(3) is a standing assumption for all instances
--   - reading: a set of ε-relevant distances for I, defined from 'the optimal solution (X*, σ*)' (Definition 3.1) → for every optimal solution (X*, σ*) some output set is ε-relevant with respect to it; reason: the proof fixes an arbitrary optimal solution and its construction 'does not use X* or σ*' (p. 80)
--   - reading: §3: 'Throughout this section, we assume k ≥ 2 and n = |P| ≥ 2' → hypotheses 2 ≤ k and 2 ≤ n; reason: standing assumption of the section containing the lemma (p. 22)
--   - encoding: poly(|I|, k, d, 1/ε) and poly(log n, k, d, ψ, 1/ε) → C·(s·k·d·⌈1/ε⌉)^e + C steps on every tape and |D| ≤ C·(log₂ n·k·d·ψ·(1/ε))^e + C, with universal C, e; reason: explicit polynomials with constants fixed before the instance
--   - encoding: sets D ⊆ R̄ containing ∞, f of a matrix with ∞ entries, 0·∞ = 0 → Finset ℝ≥0∞ with ⊤ added by the decoder; relevance requires every mapped entry finite; ENNReal's 0 * ⊤ = 0; reason: an ∞ entry makes the objective infinite; same sets
--   - encoding: linear functions h_ℓ: R^k_{≥0} → R^d_{≥0} → nonnegative coefficients c_{ℓ,j,i} with (h_ℓ z)_j = Σ_i c_{ℓ,j,i} z_i, given as input reals; reason: every such linear map has this form (p. 79 obtains the coefficients by evaluating h_ℓ on unit vectors)
--   - encoding: OPT_I, the value of 'the optimal solution' → the infimum of f(U(X, σ)) over X ∈ F^k and σ (nonempty, bounded below by 0); reason: with F infinite a minimum need not exist; equal to the minimum when it exists
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 22, Lemma 3.2

import Mathlib
import Definitions.Def_DistMapClust_Main_IO

open scoped ENNReal

namespace DistMapClust.Main

/-- Lemma 3.2 (p. 22). For every class constant `c` of §A.1(3) there are one program and universal
constants `C, e` such that, on every instance with `k ≥ 2`, `n ≥ 2` (§3's standing assumption), every
size parameter `s ≥ n, k, d, ψ` with `2^{-s^c} ≤ OPT_I ≤ 2^{s^c}`, every `ε ∈ (0, 1/48)` and every
tape, the program, given `I` and `ε`, halts within `C (s k d ⌈1/ε⌉)^e + C` steps and outputs a
collection of sets of distances, each containing `∞` and of size at most
`C (log₂ n · k d ψ / ε)^e + C`, such that for every optimal solution `(X*, σ*)` one of the sets is a
set of `ε`-relevant distances. -/
theorem lemma_3_2 :
    ∀ c : ℕ, ∃ prog : Program, Admissible prog ∧ ∃ C e : ℕ,
      ∀ (α : Type) (I : Instance α), 2 ≤ I.k → 2 ≤ I.n →
      ∀ s : ℕ, I.n ≤ s → I.k ≤ s → I.d ≤ s → I.ψ ≤ s → OptBounded s c I.OPT →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 48 → ∀ ν : Tape,
        HaltsWithin prog (I.oracles fun _ => 0) ν (I.start s ([ε] ++ I.coefList))
          ((C : ℝ) * ((s : ℝ) * I.k * I.d * ⌈1 / ε⌉₊) ^ e + C) ∧
        ∀ S, finalState prog (I.oracles fun _ => 0) ν (I.start s ([ε] ++ I.coefList)) = some S →
          (∀ m < outCount S, OutSetNonneg S m ∧
            ((outSet S m).card : ℝ) ≤
              (C : ℝ) * (Real.logb 2 I.n * I.k * I.d * I.ψ * (1 / ε)) ^ e + C) ∧
          ∀ (Xs : Fin I.k → α) (σs : Fin I.n → Fin I.ψ), I.IsOptimal Xs σs →
            ∃ m < outCount S, I.IsRelevant ε Xs σs (outSet S m) := by sorry

end DistMapClust.Main
