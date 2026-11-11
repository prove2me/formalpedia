-- Prove2me | Theorems.Thm_DistMapClust_Main_lemma_4_2
-- name    : DistMapClust.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:06:39.398112+00:00
-- url     : https://prove2.me/theorems/95e4a37d-2233-419a-b3cc-57ea107c4418
-- title:
--   Lemma 4.2 — rounding to an ε-nice instance changes every selection's cost by at most a factor 1 + 4ε
-- statement:
--   Let $I=(P,U,W,f')$ be an instance of Row-Wise Ordered Norm Mapping Selection (finite values) and $\varepsilon>0$ sufficiently small. In polynomial time one can compute a list of polynomially many instances $(P,U',W',f')$ containing an $\varepsilon$-nice instance $I'$ such that for every mapping selection $\sigma$
--   $$\mathrm{cost}_I(\sigma)\le\mathrm{cost}_{I'}(\sigma),\qquad \mathrm{cost}_{I'}(\sigma)\le(1+4\varepsilon)\,\mathrm{cost}_I(\sigma)\ \text{ if } u'(p,\sigma(p))_i\neq\infty\ \forall p,i .$$
--   Formally: there is a universal $\varepsilon_0>0$, and for every class constant $c$ a program and universal $C,e$, such that for every $\varepsilon\in(0,\varepsilon_0)$, size parameter $s\ge n,d,\psi$ with $2^{-s^c}\le\mathrm{OPT}_I\le2^{s^c}$ and every tape, the run halts within $C(s\lceil1/\varepsilon\rceil)^e+C$ steps and outputs at most $Cs^e+C$ instances, one of which is valid, $\varepsilon$-nice and satisfies both inequalities. It is the first structural step of the mapping-selection algorithm: afterwards each $i$-cost takes only $O(\log(nd/\varepsilon)/\varepsilon)$ values.
--
--   **Formalization Note.** The output instances share $n,d,\psi$ and $f'$ with $I$; their values $u'$ may be $\infty$ (flag in integer memory) and their weights $W'$ are output reals.
--
--   Differences from the source:
--   - reading: (ii) holds 'if u(p, σ(p))_i ≠ ∞ for all p ∈ P, i ∈ [d]' → (ii) holds if u′(p, σ(p))_i ≠ ∞ for all p, i (values of the ε-nice instance I′); reason: obvious typo: the values of I are finite, the literal statement is false (INSIGHTS I3), the proof uses u′
--   - reading: §4: 'We always assume ε > 0 to be sufficiently small' → there is a universal ε₀ > 0 such that the statement holds for every ε ∈ (0, ε₀); reason: the standing assumption of §4 (p. 46), with the threshold independent of the instance
--   - reading: an algorithm running in time … (bit model, §A.1; the Ball Intersection Algorithm 'supplied only as an oracle', §2.1) → one program of the unit-cost randomized oracle real RAM `DistMapClust_Main_Machine` (published SmaleNinth real-RAM core, uniform tape, no floor or other real-to-integer conversion, opaque point registers; one step per instruction including the oracles dist, ballInt, evalObj, evalNorm, evalMap, lam); reason: the paper fixes no machine; points of a possibly infinite F are reachable only through distances and the oracle (p. 8: the algorithm 'accesses only the distances')
--   - reading: in polynomial time … a list of polynomially many instances → at most C·(s·⌈1/ε⌉)^e + C steps on every tape and at most C·s^e + C output instances, universal C, e; reason: ε is part of the input; for each fixed ε this is polynomial in s, which is the paper's claim with ε a constant
--   - reading: poly(|I|), |I| the bit size, and §A.1 assumption 3: 2^{−poly(|I|)} ≤ OPT_I ≤ 2^{poly(|I|)} → a size parameter s given as input with n, k, d, ψ ≤ s; poly(|I|) = C·s^e + C with universal C, e fixed before the instance; hypothesis OptBounded s c OPT_I (2^{−s^c} ≤ OPT_I ≤ 2^{s^c}) for a class constant c quantified before the program; reason: the bit size of an instance with opaque points and infinite F has no meaning on a real RAM; §A.1(3) is a standing assumption for all instances
--   - encoding: u(p, ℓ)_i ∈ R≥0 ∪ {∞}, cost of a selection meeting ∞ → values in ℝ≥0∞; cost_I(σ) = ∞ when some selected value is ∞, else ofReal(f′((ord_{w_i}(…))_i)); reason: an ∞ entry makes the objective infinite; same instances
--   - reading: Definition 4.1(2): 'for the optimal mapping selection σ of I' → for every optimal mapping selection; reason: optimal selections need not be unique; the proof shows it for every optimal selection (any selection with an ∞ value has infinite cost)
--   - encoding: index sets [k], [d], [ψ], [n] (1-based) → Fin k, Fin d, Fin ψ, Fin n (0-based); P an injective family Fin n → α; reason: Lean convention; same instances
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 47, Lemma 4.2

import Mathlib
import Definitions.Def_DistMapClust_Main_IO

open scoped ENNReal

namespace DistMapClust.Main

/-- Lemma 4.2 (p. 47), for `ε` sufficiently small (§4's standing assumption: there is a universal
`ε₀ > 0`). Given an instance `I = (P, U, W, f')` (all values finite) and `ε`, one program computes,
in time `C (s ⌈1/ε⌉)^e + C`, a list of at most `C s^e + C` instances `(P, U', W', f')` containing an
`ε`-nice instance `I'` such that for every selection `σ`: (i) `cost_I(σ) ≤ cost_{I'}(σ)`, and
(ii) `cost_{I'}(σ) ≤ (1 + 4ε) cost_I(σ)` if `u'(p, σ(p))ᵢ ≠ ∞` for all `p, i` (the condition is read on
the values `u'` of `I'`). -/
theorem lemma_4_2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ c : ℕ, ∃ prog : Program, Admissible prog ∧ ∃ C e : ℕ,
      ∀ I : SelInstance, I.Valid → (∀ p ℓ i, I.U p ℓ i ≠ ⊤) →
      ∀ s : ℕ, I.n ≤ s → I.d ≤ s → I.ψ ≤ s → OptBounded s c I.OPT.toReal →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ ν : Tape,
        HaltsWithin prog I.oracles ν (I.start s ε)
          ((C : ℝ) * ((s : ℝ) * ⌈1 / ε⌉₊) ^ e + C) ∧
        ∀ S, finalState prog I.oracles ν (I.start s ε) = some S →
          (outCount S : ℝ) ≤ (C : ℝ) * (s : ℝ) ^ e + C ∧
          ∃ m < outCount S, (outSelInstance S I m).Valid ∧ (outSelInstance S I m).IsNice ε ∧
            ∀ σ : Fin I.n → Fin I.ψ,
              I.cost σ ≤ (outSelInstance S I m).cost σ ∧
              ((∀ p i, (outSelInstance S I m).U p (σ p) i ≠ ⊤) →
                (outSelInstance S I m).cost σ ≤ ENNReal.ofReal (1 + 4 * ε) * I.cost σ) := by sorry

end DistMapClust.Main
